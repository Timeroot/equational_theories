import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1560`: `x = (y ◇ z) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_pyx_x_pyx_Equation1560 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1560 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1560.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
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
  have eq32 : y = (τ (σ y)) := by
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq134 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq51
    | (have j0 := eq51 (M.op x y)
       grind)
    | exact resolve eq51 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq175 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op (M.op X0 (M.op X3 X0)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq16 X0 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X0) X1 X0
       have i₂ := eq16 X0 X0 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : x ≠ (M.op x y) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq175 (M.op y y)
       have i₂ := eq16 y y y
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq190 : y ≠ (M.op (M.op x y) y) ∨ (k y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq185
       grind)
    | exact superpose eq185 eq13
    | exact resolve eq13 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op y (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 y
       have i₂ := eq185
       grind)
    | exact superpose eq185 eq16
    | exact resolve eq16 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq176 (M.op sF3 sF3)
       have i₂ := eq16 sF3 sF3 sF3
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : ∀ X1 : G, (M.op (σ y) (M.op X1 (M.op (M.op (σ y) (M.op (σ x) (σ y))) X1))) = X1 := by
    intro X1
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 (M.op X2 X0)
       have i₂ := eq181 X0 X2
       grind)
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq349 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq624 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq625 : (k y y) = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq185
       grind)
    | exact superpose eq185 eq28
    | exact resolve eq28 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq630 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq701 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq636 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq636 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq636 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq702 : (k y y) = (M.op (M.op x y) y) := by
    first
    | (have r₁ := eq625
       have r₂ := eq190
       grind)
    | exact resolve eq625 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq625
  have eq711 : x ≠ (M.op x y) ∨ y = (M.op y x) ∨ y = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq717 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq624
       grind)
    | exact superpose eq624 eq40
    | exact resolve eq40 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq728 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq727
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq727
    | exact resolve eq727 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq730 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq728
    | exact resolve eq728 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq751 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq730 eq630
    | exact resolve eq630 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq751
       have r₂ := eq27
       grind)
    | exact resolve eq751 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq764 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq758 eq179
    | exact resolve eq179 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq765 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq758 eq183
    | (have r₁ := eq183
       have r₂ := eq758
       grind)
    | exact resolve eq183 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq766 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq758 eq193
    | exact resolve eq193 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq768 : ∀ X0 : G, (M.op (σ y) (M.op X0 (M.op (M.op (σ y) (σ x)) X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq758 eq205
    | exact resolve eq205 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq770 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq765
  have eq771 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq766
    | exact resolve eq766 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq766
  have eq772 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (k (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq770 eq764
    | exact resolve eq764 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq773 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq758 eq771
    | exact resolve eq771 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq776 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq773 eq176
    | exact resolve eq176 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq778 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq773 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq780 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq773 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq773
       grind)
    | exact resolve eq13 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq781 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq773 eq16
    | exact resolve eq16 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq783 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (k (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq770 eq781
    | exact resolve eq781 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq785 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq778
       have r₂ := eq780
       grind)
    | exact resolve eq778 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778 eq780
  have eq786 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq758 eq776
    | exact resolve eq776 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq789 : (σ y) = (M.op (σ x) (k (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq770 eq786
    | exact resolve eq786 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq791 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq785 eq116
    | exact resolve eq116 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq796 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq791
    | exact resolve eq791 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq791
  have eq806 : (σ y) = (M.op (k (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq770 eq179
    | exact resolve eq179 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : (σ y) = (M.op (k (σ x) (σ y)) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq758 eq806
    | exact resolve eq806 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq817 : (σ y) = (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq770 eq814
    | exact resolve eq814 eq770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq770 eq814
  have eq823 : (M.op (k (σ x) (σ y)) (k (σ x) (σ y))) = (M.op (σ y) (k (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq789 eq181
    | exact resolve eq181 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq825 : ∀ X0 : G, (k (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (M.op (k (σ x) (σ y)) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq789 eq16
    | exact resolve eq16 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq828 : (σ y) = (M.op (σ y) (k (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq817 eq823
    | exact resolve eq823 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817 eq823
  have eq834 : (σ y) ≠ (σ y) ∨ (M.op (k (σ x) (σ y)) (σ y)) = (k (σ y) (k (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq828 eq13
    | (have j0 := eq13 (σ y) (k (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (σ y) (k (σ x) (σ y))
       have r₂ := eq828
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq828
       grind)
    | exact resolve eq13 eq828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq837 : (M.op (k (σ x) (σ y)) (σ y)) = (k (σ y) (k (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq834
  have eq990 : (k (σ x) (σ y)) = (M.op (σ y) (M.op (k (σ x) (σ y)) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq772 eq768
    | exact resolve eq768 eq772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq1004 : (k (σ x) (σ y)) = (M.op (σ y) (M.op (k (σ x) (σ y)) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq990
  have eq1017 : (k (σ x) (σ y)) = (M.op (σ y) (k (σ y) (k (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq837 eq1004
    | exact resolve eq1004 eq837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1265 : (M.op (k (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (k (σ x) (σ y)) (σ y)) (k (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq825 eq768
    | exact resolve eq768 eq825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq1272 : (M.op (k (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (k (σ x) (σ y)) (σ y)) (k (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq1265
  have eq1282 : (M.op (σ y) (σ y)) = (M.op (k (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq783 eq1272
    | exact resolve eq1272 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783 eq1272
  have eq1290 : (σ x) = (M.op (k (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq773 eq1282
    | exact resolve eq1282 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773 eq1282
  have eq1294 : ∀ X0 : G, (k (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1290 eq825
    | exact resolve eq825 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825
  have eq1295 : (σ x) = (k (σ y) (k (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1290 eq837
    | exact resolve eq837 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837 eq1290
  have eq1306 : (σ x) = (k (σ y) (k (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq1295
  have eq1307 : ∀ X0 : G, (k (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1294 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1294
  have eq1313 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1307 x
       have i₂ := eq181 sF2 x
       grind)
    | exact superpose eq181 eq1307
    | exact resolve eq1307 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307
  have eq1343 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1313 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq1313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1345 : (σ x) ≠ (k (σ x) (σ y)) ∨ (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1313 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq1313
       grind)
    | exact resolve eq13 eq1313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1313
  have eq1357 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1343
       have r₂ := eq1345
       grind)
    | exact resolve eq1343 eq1345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343 eq1345
  have eq1415 : (k (σ x) (σ x)) = (M.op (σ y) (k (σ y) (k (σ x) (σ x)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1357 eq1017
    | exact resolve eq1017 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017
  have eq1421 : (σ x) = (k (σ y) (k (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1357 eq1306
    | exact resolve eq1306 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306
  have eq1424 : (σ y) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1357 eq701
    | (have j0 := eq701 (σ x) (σ y)
       grind)
    | exact resolve eq701 eq1357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357
  have eq1426 : (σ x) = (k (σ y) (k (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq1421
  have eq1432 : (k (σ x) (σ x)) = (M.op (σ y) (k (σ y) (k (σ x) (σ x)))) ∨ x = (M.op x y) := by grind
  clear eq1415
  have eq1446 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) ≠ (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq1424
    | exact resolve eq1424 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1424
  have eq1452 : (k (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1426 eq1432
    | exact resolve eq1432 eq1426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1426 eq1432
  have eq1458 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq730 eq1446
    | exact resolve eq1446 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446
  have eq1464 : (σ y) ≠ (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1458
       have r₂ := eq27
       grind)
    | exact resolve eq1458 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1458
  have eq1923 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq758 eq717
    | (have r₁ := eq717
       have r₂ := eq758
       grind)
    | exact resolve eq717 eq758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717 eq758
  have eq1924 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq1923
  have eq1925 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq730 eq1924
    | exact resolve eq1924 eq730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq730 eq1924
  have eq1929 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1925 eq1452
    | exact resolve eq1452 eq1925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1452 eq1925
  have eq1960 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1929
  have eq1974 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1960
       have r₂ := eq1464
       grind)
    | exact resolve eq1960 eq1464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1464 eq1960
  have eq1983 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1974 eq29
    | exact resolve eq29 eq1974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq1991 : (k (M.op x y) (M.op x y)) = (τ (k (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1974 eq134
    | exact resolve eq134 eq1974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq1974
  have eq1996 : (k y y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq116 eq1991
    | exact resolve eq1991 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq1991
  have eq2004 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq1983
    | exact resolve eq1983 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1983
  have eq2005 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq796 eq1996
    | exact resolve eq1996 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq1996
  have eq2011 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2004
       grind)
    | exact superpose eq2004 eq18
    | exact resolve eq18 eq2004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2022 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq702
       have i₂ := eq2004
       grind)
    | exact superpose eq2004 eq702
    | exact resolve eq702 eq2004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2004
  have eq2037 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2005 eq2022
    | exact resolve eq2022 eq2005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2005 eq2022
  have eq2076 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2037 eq181
    | exact resolve eq181 eq2037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2037
  have eq2079 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2011 eq2076
    | exact resolve eq2076 eq2011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2011 eq2076
  have eq2080 : x = (M.op x y) := by grind
  clear eq2079
  have eq2082 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2080
       grind)
    | exact superpose eq2080 eq18
    | exact resolve eq18 eq2080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2083 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq2080
       grind)
    | exact superpose eq2080 eq22
    | exact resolve eq22 eq2080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq2084 : ∀ X0 : G, (k (σ x) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq2080
       grind)
    | exact superpose eq2080 eq36
    | exact resolve eq36 eq2080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq2085 : ∀ X0 : G, (k (σ X0) (σ x)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq2080
       grind)
    | exact superpose eq2080 eq40
    | exact resolve eq40 eq2080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq2087 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq182
       have i₂ := eq2080
       grind)
    | exact superpose eq2080 eq182
    | (have r₁ := eq182
       have r₂ := eq2080
       grind)
    | exact resolve eq182 eq2080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq2088 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op y (M.op x y)) ∨ y = (k y (M.op x y)) := by
    first
    | (have i₁ := eq711
       have i₂ := eq2080
       grind)
    | exact superpose eq2080 eq711
    | (have r₁ := eq711
       have r₂ := eq2080
       grind)
    | exact resolve eq711 eq2080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq2080
  have eq2089 : y = (k y (M.op x y)) ∨ y = (M.op y (M.op x y)) := by grind
  clear eq2088
  have eq2090 : (k (M.op x y) y) = (M.op y (M.op x y)) := by grind
  clear eq2087
  have eq2093 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2083 eq20
    | exact resolve eq20 eq2083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2103 : ∀ X0 : G, (τ (k X0 (σ x))) = (k (τ X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2083 eq349
    | exact resolve eq349 eq2083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349 eq2083
  have eq2155 : (M.op x y) = (k y y) := by
    first
    | exact superpose eq2082 eq702
    | exact resolve eq702 eq2082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2158 : y = (M.op (M.op x y) (M.op y (M.op x y))) := by
    first
    | exact superpose eq2082 eq191
    | exact resolve eq191 eq2082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq2082
  have eq2168 : y = (M.op (M.op x y) (k (M.op x y) y)) := by
    first
    | exact superpose eq2090 eq2158
    | exact resolve eq2158 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2158
  have eq2175 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq2155
       grind)
    | exact superpose eq2155 eq41
    | exact resolve eq41 eq2155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq2182 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2175
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2175
    | exact resolve eq2175 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2175
  have eq2185 : (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq2182
    | exact resolve eq2182 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2182
  have eq2188 : (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq2093 eq2185
    | exact resolve eq2185 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2185
  have eq2236 : y = (k (k (M.op x y) y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2168 eq28
    | exact resolve eq28 eq2168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2168
  have eq2997 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq2089 eq2085
    | exact resolve eq2085 eq2089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2089
  have eq3003 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq2997
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2997
    | exact resolve eq2997 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2997
  have eq3009 : (σ y) = (k (σ y) (σ x)) ∨ y = (k (M.op x y) y) := by
    first
    | exact superpose eq2090 eq3003
    | exact resolve eq3003 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2090 eq3003
  have eq3020 : (τ (σ y)) = (k (τ (σ y)) (M.op x y)) ∨ y = (k (M.op x y) y) := by
    first
    | exact superpose eq3009 eq2103
    | exact resolve eq2103 eq3009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3009
  have eq3028 : y = (k (M.op x y) y) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq32 eq3020
    | exact resolve eq3020 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3020
  have eq3056 : y = (k y (M.op x y)) ∨ y = (M.op x y) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq3028 eq2236
    | exact resolve eq2236 eq3028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2236
  have eq3060 : (σ y) = (k (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq3028 eq2084
    | exact resolve eq2084 eq3028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2084
  have eq3065 : y ≠ y ∨ (k y (M.op x y)) = (M.op (M.op x y) y) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq3028 eq701
    | (have j0 := eq701 (M.op x y) y
       grind)
    | (have r₁ := eq701 (M.op x y) y
       have r₂ := eq3028
       grind)
    | exact resolve eq701 eq3028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3028
  have eq3068 : (k y (M.op x y)) = (M.op (M.op x y) y) ∨ y = (k y (M.op x y)) := by grind
  clear eq3065
  have eq3069 : y = (k y (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq3056
  have eq3071 : (k y y) = (k y (M.op x y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq702 eq3068
    | exact resolve eq3068 eq702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702 eq3068
  have eq3074 : (σ y) = (k (σ x) (σ y)) ∨ y = (k y (M.op x y)) := by
    first
    | (have i₁ := eq3060
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3060
    | exact resolve eq3060 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3060
  have eq3082 : (M.op x y) = (k y (M.op x y)) ∨ y = (k y (M.op x y)) := by
    first
    | (have i₁ := eq3071
       have i₂ := eq2155
       grind)
    | exact superpose eq2155 eq3071
    | exact resolve eq3071 eq2155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155 eq3071
  have eq3091 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq3069 eq3082
    | exact resolve eq3082 eq3069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3082
  have eq3188 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq3074 eq701
    | (have j0 := eq701 (σ x) (σ y)
       grind)
    | (have r₁ := eq701 (σ x) (σ y)
       have r₂ := eq3074
       grind)
    | exact resolve eq701 eq3074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701 eq3074
  have eq3191 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y (M.op x y)) := by grind
  clear eq3188
  have eq3192 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq26 eq3191
    | exact resolve eq3191 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3191
  have eq3666 : (k (τ (σ y)) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq3192 eq2103
    | exact resolve eq2103 eq3192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2103 eq3192
  have eq3674 : (k y (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq32 eq3666
    | exact resolve eq3666 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq3666
  have eq3678 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ y = (k y (M.op x y)) := by
    first
    | exact superpose eq3069 eq3674
    | exact resolve eq3674 eq3069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3069 eq3674
  have eq3682 : y = (k y (M.op x y)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3091 eq3678
    | exact resolve eq3678 eq3091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3091 eq3678
  have eq3693 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq3682 eq2085
    | exact resolve eq2085 eq3682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2085 eq3682
  have eq3700 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq3693
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3693
    | exact resolve eq3693 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3693
  have eq3709 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3700 eq630
    | exact resolve eq630 eq3700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630 eq3700
  have eq4230 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3709 eq14
    | exact resolve eq14 eq3709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3709
  have eq4233 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq4230
    | exact resolve eq4230 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4230
  have eq4236 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq4233
       have r₂ := eq27
       grind)
    | exact resolve eq4233 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4233
  have eq4241 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4236 eq179
    | exact resolve eq179 eq4236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq4252 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq8255 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (k (σ y) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq4241 X0
       have i₂ := eq28 sF3 sF3
       grind)
    | exact superpose eq28 eq4241
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq4241 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4241
  have eq8282 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq2188 eq8255
    | exact resolve eq8255 eq2188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8255
  have eq8284 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq8282 x
       have i₂ := eq181 sF2 x
       grind)
    | exact superpose eq181 eq8282
    | exact resolve eq8282 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8282
  have eq20683 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq8284 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq8284
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq8284
       grind)
    | exact resolve eq13 eq8284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8284
  have eq20708 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq20683
  have eq20720 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2188 eq20708
    | exact resolve eq20708 eq2188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2188 eq20708
  have eq20732 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq20720
       have r₂ := eq4252
       grind)
    | exact resolve eq20720 eq4252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20720
  have eq20757 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq20732 eq217
    | exact resolve eq217 eq20732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq20765 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq20732 eq180
    | exact resolve eq180 eq20732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq20766 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20732 eq181
    | exact resolve eq181 eq20732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq20732
  have eq20792 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq20765
    | (have j0 := eq20765 X0 X1
       grind)
    | exact resolve eq20765 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20765
  have eq20796 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq20757
    | (have j0 := eq20757 X0 X1
       grind)
    | exact resolve eq20757 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq20757
  have eq20804 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op X1 (σ x))) (M.op (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq4236 eq20792
    | exact resolve eq20792 eq4236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20792
  have eq20807 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op X1 (σ x))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq4236 eq20796
    | exact resolve eq20796 eq4236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4236 eq20796
  have eq20810 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op X1 (σ x))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq20766 eq20804
    | exact resolve eq20804 eq20766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20766 eq20804
  have eq20811 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f20811_13 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op X1 (σ x))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      grind
    have f20811_14 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op X1 (σ x))) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
      intro X0 X1
      grind
    have f20811_23 : (σ y) ≠ (σ x) := by grind
    have f20811_24 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
    have f20811_26 : ∀ X0 X1 : G, (σ x) = (M.op (M.op X0 (M.op X1 (σ x))) (σ y)) := by
      intro X0 X1
      first
      | (have j0 := f20811_14 X0 X1
         grind)
      | (have r₁ := f20811_14 X0 X1
         have r₂ := f20811_24
         grind)
      | exact resolve f20811_14 f20811_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f20811_27 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op X1 (σ x))) (σ y)) := by
      intro X0 X1
      first
      | (have j0 := f20811_13 X0 X1
         grind)
      | (have r₁ := f20811_13 X0 X1
         have r₂ := f20811_24
         grind)
      | exact resolve f20811_13 f20811_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f20811_28 : (σ y) = (σ x) := by
      first
      | (have i₁ := f20811_27 x x
         have i₂ := f20811_26 x x
         grind)
      | exact superpose f20811_26 f20811_27
      | exact resolve f20811_27 f20811_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f20811_29 : False := by
      first
      | (have r₁ := f20811_28
         have r₂ := f20811_23
         grind)
      | exact resolve f20811_28 f20811_23
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f20811_29
  clear eq20807 eq20810
  have eq20812 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq20811
       have r₂ := eq4252
       grind)
    | exact resolve eq20811 eq4252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4252 eq20811
  have eq20816 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq20812 eq27
    | exact resolve eq27 eq20812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20812
  have eq20863 : False := by grind
  exact eq20863

/-- `Equation1577`: `x = (y ◇ z) ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pxy_pxx_pxy_Equation1577 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1577 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1577.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (M.op X2 X0))) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : y = (τ (σ y)) := by
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
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (σ (k X1 (k x X0))) = (k (σ X1) (k (σ x) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq10
    | exact resolve eq10 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq73 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq134 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq51
    | (have j0 := eq51 (M.op x y)
       grind)
    | exact resolve eq51 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq153 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq73 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq73
    | exact resolve eq73 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq175 : ∀ X0 : G, (M.op (M.op x y) (M.op x (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) (M.op (M.op X1 (M.op X2 X0)) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op X1 X2) (M.op X1 (M.op X2 X0))
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, y = (M.op (M.op X0 x) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ x)) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op (M.op X1 (M.op X2 X3)) (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X2 (M.op X3 X0)) X1 (M.op X2 X3)
       have i₂ := eq16 X0 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op (M.op X1 X2) X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X2 X0) (M.op X1 X2) X1
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) ≠ X0 ∨ (k (M.op X1 (M.op X2 X0)) (M.op X1 X2)) = (M.op (M.op X1 (M.op X2 X0)) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 (M.op X2 X0)) (M.op X1 X2)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 (M.op X1 (M.op X2 X0)) (M.op X1 X2)
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) ≠ X0 ∨ (k (M.op X1 (M.op X2 X0)) (M.op X1 X2)) = (M.op X2 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq184 X0 X1 X2
       have i₂ := eq180 X2 X1 X2 X0
       grind)
    | exact superpose eq180 eq184
    | (have j0 := eq184 X0 X1 X2
       grind)
    | exact resolve eq184 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq186 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (M.op x (M.op y X0)) = (M.op (M.op X1 (M.op x y)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : y = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq186 eq178
    | exact resolve eq178 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op x X0))) = X0 := by
    intro X0
    first
    | exact superpose eq186 eq16
    | exact resolve eq16 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq190 eq179
    | exact resolve eq179 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq190 eq16
    | exact resolve eq16 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq362 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq240 eq16
    | exact resolve eq16 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq362 eq16
    | exact resolve eq16 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq504 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq615 : ∀ X0 X1 X2 : G, (k (M.op X1 X2) (M.op X1 (M.op X2 X0))) = X0 ∨ (M.op X1 X2) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 (M.op X1 X2) (M.op X1 (M.op X2 X0))
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq28
    | exact resolve eq28 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq620 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq624 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq629 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X2 (k X0 X1))) = X1 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq703 : x ≠ (M.op x y) ∨ x = (M.op y x) ∨ (k x y) = (M.op x x) := by
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
  have eq708 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq728 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq620
       grind)
    | exact superpose eq620 eq41
    | exact resolve eq41 eq620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620
  have eq729 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq728
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq728
    | exact resolve eq728 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq731 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq729
    | exact resolve eq729 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq739 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq731 eq624
    | exact resolve eq624 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq746 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq739
       have r₂ := eq27
       grind)
    | exact resolve eq739 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739
  have eq750 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq746 eq27
    | exact resolve eq27 eq746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (M.op (σ y) X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq746 eq176
    | exact resolve eq176 eq746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq755 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq746 eq239
    | exact resolve eq239 eq746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq759 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) (M.op (σ x) X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq746 eq387
    | exact resolve eq387 eq746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387
  have eq803 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (M.op (M.op (σ x) (M.op (σ y) X0)) X1))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq751 eq16
    | exact resolve eq16 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1368 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) X3) = (M.op (M.op X0 (M.op X1 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq181 X3 (M.op X1 X2) (M.op X1 (M.op X2 X0))
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq181
    | exact resolve eq181 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1413 : ∀ X0 : G, (σ y) = (M.op X0 (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq179 (M.op sF2 x)
       have i₂ := eq181 (M.op (M.op sF2 x) sF4) sF2 x
       grind)
    | exact superpose eq181 eq179
    | exact resolve eq179 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1640 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (M.op (σ x) (M.op (M.op (σ x) X0) X1))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq240 eq803
    | exact resolve eq803 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq1800 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) (M.op (σ x) (M.op (M.op (σ x) X0) X1))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1640 X0 X1
       have i₂ := eq1368 X0 sF4 sF2 (M.op sF2 (M.op (M.op sF2 X0) X1))
       grind)
    | (have i₁ := eq1640 x X1
       have i₂ := eq1368 sF4 sF2 x (M.op sF2 (M.op (M.op sF2 x) X1))
       grind)
    | exact superpose eq1368 eq1640
    | exact resolve eq1640 eq1368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1640
  have eq1850 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) X1))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq1800 x X1
       have i₂ := eq180 (M.op (M.op sF2 x) X1) sF2 x sF4
       grind)
    | exact superpose eq180 eq1800
    | exact resolve eq1800 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800
  have eq1883 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (M.op (M.op (σ x) X0) X1))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq746 eq1850
    | exact resolve eq1850 eq746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1850
  have eq2193 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (σ x) X0)) (M.op (σ x) (M.op X0 X1))) = X1 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq759 eq1883
    | exact resolve eq1883 eq759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq2194 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op (σ y) X0)) (M.op (σ x) (M.op X0 X1))) = X1 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq751 eq1883
    | exact resolve eq1883 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751 eq1883
  have eq2310 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op (σ y) X0)) (M.op (σ x) (M.op X0 X1))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq2194 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2194
  have eq2311 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (σ x) X0)) (M.op (σ x) (M.op X0 X1))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq2193 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193
  have eq2350 : ∀ X0 X1 : G, (M.op (σ y) (M.op X0 (M.op X0 X1))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq2310 x X1
       have i₂ := eq180 (M.op x X1) sF2 sF3 x
       grind)
    | exact superpose eq180 eq2310
    | exact resolve eq2310 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2310
  have eq2351 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op X0 (σ y))) (M.op (σ x) (M.op X0 X1))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq2311 X0 X1
       have i₂ := eq1368 X0 sF3 sF2 (M.op sF2 (M.op X0 X1))
       grind)
    | (have i₁ := eq2311 x X1
       have i₂ := eq1368 sF3 sF2 x (M.op sF2 (M.op x X1))
       grind)
    | exact superpose eq1368 eq2311
    | exact resolve eq2311 eq1368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2311
  have eq2372 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) (M.op X0 X1))) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq2351 x X1
       have i₂ := eq180 (M.op x X1) sF2 x sF3
       grind)
    | exact superpose eq180 eq2351
    | exact resolve eq2351 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2351
  have eq2410 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (σ y) (M.op (M.op X1 X2) X0)) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2350 (M.op X1 X2) (M.op X1 (M.op X2 X0))
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq2350
    | exact resolve eq2350 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2421 : y = (M.op (σ y) (M.op x (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2350 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2350
    | (have j0 := eq2350 x y
       grind)
    | exact resolve eq2350 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2476 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op (σ y) X1) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2350 eq16
    | exact resolve eq16 eq2350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2480 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ y) (M.op (M.op X1 (M.op X1 X0)) X2))) = X2 ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq2350 eq16
    | exact resolve eq16 eq2350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2483 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 X0)) X2) = (M.op (M.op X0 (σ y)) X2) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq2350 eq181
    | exact resolve eq181 eq2350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2350
  have eq2534 : ∀ X0 X2 : G, (M.op X0 (M.op (σ y) (M.op (M.op X0 (σ y)) X2))) = X2 ∨ x = (M.op x y) := by
    intro X0 X2
    first
    | exact superpose eq2483 eq2480
    | exact resolve eq2480 eq2483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2480 eq2483
  have eq2573 : ∀ X0 X2 : G, (M.op X0 (M.op X0 (M.op (σ y) X2))) = X2 ∨ x = (M.op x y) := by
    intro X0 X2
    first
    | exact superpose eq2410 eq2534
    | exact resolve eq2534 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2534
  have eq2592 : ∀ X0 : G, (M.op y (M.op (σ y) (M.op (M.op x (M.op x y)) X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2421 eq16
    | exact resolve eq16 eq2421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2606 : ∀ X0 : G, (M.op y (M.op x (M.op (M.op x y) X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2410 eq2592
    | exact resolve eq2592 eq2410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2410 eq2592
  have eq2651 : y = (M.op x (M.op (σ y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2372 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2372
    | (have j0 := eq2372 x y
       grind)
    | exact resolve eq2372 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2697 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2372 eq16
    | exact resolve eq16 eq2372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2872 : ∀ X0 : G, (M.op (M.op (σ y) (M.op x y)) X0) = (M.op (M.op y x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2651 eq181
    | exact resolve eq181 eq2651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2877 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op y x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2476 eq2872
    | exact resolve eq2872 eq2476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2872
  have eq2976 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x (M.op x y)) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2421 eq2476
    | exact resolve eq2476 eq2421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2421 eq2476
  have eq3075 : ∀ X0 : G, (M.op y X0) = (M.op (M.op x (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2976 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2976
  have eq3129 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq755 eq2573
    | exact resolve eq2573 eq755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3176 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op X1 X1) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2573 eq16
    | exact resolve eq16 eq2573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3273 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3129 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3129
  have eq3829 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) X0)) = (M.op X1 (M.op (M.op X2 X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 X1 X2 X3 (M.op X2 (M.op (M.op X3 X1) X0))
       have i₂ := eq16 X0 X2 (M.op X3 X1)
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4458 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X0 X1)) (M.op (M.op X3 X2) X4)) = (M.op (M.op X5 (M.op X0 (M.op X1 X2))) (M.op X5 X4)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq180 X4 X5 (M.op X3 (M.op X0 X1)) (M.op X3 X2)
       have i₂ := eq180 X2 X3 X0 X1
       grind)
    | exact superpose eq180 eq180
    | exact resolve eq180 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4559 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) X1)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq240 eq180
    | exact resolve eq180 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4578 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 (M.op X4 X0)))) = (M.op (M.op (M.op X3 X4) (M.op X1 X2)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq180 (M.op X3 (M.op X4 X0)) (M.op X3 X4) X1 X2
       have i₂ := eq16 X0 X3 X4
       grind)
    | exact superpose eq16 eq180
    | exact resolve eq180 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4716 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op X0 (M.op (σ x) (σ y))) X1)) = (M.op X0 (M.op (σ y) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4559 X1 X0
       have i₂ := eq3829 X0 X1 sF4 sF2
       grind)
    | (have i₁ := eq4559 x X0
       have i₂ := eq3829 X0 sF4 sF2 x
       grind)
    | exact superpose eq3829 eq4559
    | exact resolve eq4559 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4559
  have eq4789 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X0 X1)) (M.op (M.op X3 X2) X4)) = (M.op X0 (M.op (M.op X1 X2) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4458 X0 X1 X2 X3 X4 x
       have i₂ := eq180 X4 x X0 (M.op X1 X2)
       grind)
    | exact superpose eq180 eq4458
    | exact resolve eq4458 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4458
  have eq4870 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X2) X4)) = (M.op X3 (M.op (M.op X2 (M.op X3 (M.op X0 X1))) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq4789 X0 X1 X2 X3 X4
       have i₂ := eq3829 X4 (M.op X3 (M.op X0 X1)) X3 X2
       grind)
    | (have i₁ := eq4789 X0 X1 X1 X3 X0
       have i₂ := eq3829 X0 X1 (M.op X3 (M.op X0 X1)) X3
       grind)
    | exact superpose eq3829 eq4789
    | exact resolve eq4789 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4789
  have eq4987 : ∀ X0 : G, (M.op x X0) = (M.op (M.op (M.op x y) y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq181 X0 y x
       have i₂ := eq2877 y
       grind)
    | exact superpose eq2877 eq181
    | exact resolve eq181 eq2877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2877
  have eq5254 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op x (M.op x y))) (M.op X1 (M.op y X0))) = X0 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq3075 eq16
    | exact resolve eq16 eq3075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3075
  have eq5322 : ∀ X0 : G, (M.op x (M.op (M.op x y) (M.op y X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq5254 X0 x
       have i₂ := eq180 (M.op y X0) x x sF0
       grind)
    | exact superpose eq180 eq5254
    | exact resolve eq5254 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5254
  have eq5623 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3273 eq16
    | exact resolve eq16 eq3273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3273
  have eq6531 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op (M.op x y) y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq210 eq5322
    | exact resolve eq5322 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5322
  have eq7369 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq746 eq708
    | (have r₁ := eq708
       have r₂ := eq746
       grind)
    | exact resolve eq708 eq746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq708 eq746
  have eq7370 : (σ x) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq7369
  have eq7371 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq731 eq7370
    | exact resolve eq7370 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7370
  have eq7522 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (k (M.op X0 y) (M.op X0 y)) ∨ (M.op X0 y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq210 eq615
    | (have j0 := eq615 (k (M.op X0 y) (M.op X0 y)) (M.op x y) (M.op x y)
       grind)
    | exact resolve eq615 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7938 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7371 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq7371
       grind)
    | exact resolve eq13 eq7371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7371
  have eq7953 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq7938
  have eq7972 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq7953
    | exact resolve eq7953 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7953
  have eq7984 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq731 eq7972
    | exact resolve eq7972 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731 eq7972
  have eq7987 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7984
       have r₂ := eq27
       grind)
    | exact resolve eq7984 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7984
  have eq7991 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7987 eq755
    | exact resolve eq755 eq7987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq755
  have eq8008 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7987 eq5623
    | exact resolve eq5623 eq7987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5623
  have eq8014 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7987 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq7987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7987
  have eq8027 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq8008
  have eq8042 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq7991
  have eq8046 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8014
       have r₂ := eq750
       grind)
    | exact resolve eq8014 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750 eq8014
  have eq8071 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8042 eq2573
    | exact resolve eq2573 eq8042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8084 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8042 eq2372
    | exact resolve eq2372 eq8042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2372 eq8042
  have eq8085 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq8084
  have eq8088 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq8071 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8071
  have eq8126 : (τ (σ (M.op x y))) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8046 eq98
    | exact resolve eq98 eq8046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq8046
  have eq8133 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq8126
    | exact resolve eq8126 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq8126
  have eq8147 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8027 eq13
    | exact resolve eq13 eq8027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8150 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8027 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq8027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8027
  have eq8169 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq8147
       have r₂ := eq8150
       grind)
    | exact resolve eq8147 eq8150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8147 eq8150
  have eq8175 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8169 eq134
    | exact resolve eq134 eq8169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq8169
  have eq8182 : y = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq32 eq8175
    | exact resolve eq8175 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8175
  have eq8405 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8085 eq2573
    | exact resolve eq2573 eq8085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2573 eq8085
  have eq8432 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq8405 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8405
  have eq8612 : (M.op (M.op x y) (σ y)) = (M.op y (M.op x (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8088 eq2606
    | exact resolve eq2606 eq8088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2606 eq8088
  have eq8661 : (M.op (M.op x y) (σ y)) = (M.op y (M.op x (σ (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq8612
  have eq10086 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op X0 (M.op x y))) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq629 x x X0
       have i₂ := eq8133
       grind)
    | exact superpose eq8133 eq629
    | (have j0 := eq629 x x x
       grind)
    | exact resolve eq629 eq8133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq10213 : x = (M.op x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq178 eq10086
    | exact resolve eq10086 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10086
  have eq10847 : x ≠ x ∨ x = (k x x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq10213
       grind)
    | exact superpose eq10213 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq10213
       grind)
    | exact resolve eq13 eq10213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10213
  have eq10863 : x = (k x x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq10847
  have eq10876 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq8133 eq10863
    | exact resolve eq10863 eq8133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8133 eq10863
  have eq10877 : x = (M.op x y) ∨ x = y := by grind
  clear eq10876
  have eq12157 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op x y) y) (M.op x (σ (M.op x y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4987 eq8432
    | exact resolve eq8432 eq4987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4987 eq8432
  have eq12343 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op x y) y) (M.op x (σ (M.op x y)))) ∨ x = (M.op x y) := by grind
  clear eq12157
  have eq12427 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op x y) x) (M.op x (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10877 eq12343
    | exact resolve eq12343 eq10877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12343
  have eq12462 : (M.op (σ y) (σ y)) = (M.op y (M.op x (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq186 eq12427
    | exact resolve eq12427 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12427
  have eq12480 : (M.op (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8661 eq12462
    | exact resolve eq12462 eq8661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8661 eq12462
  have eq12528 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (M.op x y) (σ y)) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12480 eq3176
    | exact resolve eq3176 eq12480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3176 eq12480
  have eq12547 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (M.op x y) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq12528 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12528
  have eq12585 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2697 eq12547
    | exact resolve eq12547 eq2697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2697 eq12547
  have eq13126 : y = (M.op x (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12585 eq2651
    | exact resolve eq2651 eq12585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2651 eq12585
  have eq13256 : y = (M.op x (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq13126
  have eq13377 : x = (M.op x (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10877 eq13256
    | exact resolve eq13256 eq10877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10877 eq13256
  have eq15294 : x = (M.op x (k (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq13377
       have i₂ := eq28 sF0 sF0
       grind)
    | exact superpose eq28 eq13377
    | (have j1 := eq28 x (k (M.op x y) (M.op x y))
       grind)
    | exact resolve eq13377 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15341 : x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq8182 eq15294
    | exact resolve eq15294 eq8182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15294
  have eq15346 : x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq15341
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15341
    | exact resolve eq15341 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15341
  have eq15347 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq15346
  have eq15368 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15347 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq15347
       grind)
    | exact resolve eq13 eq15347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15386 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq15368
  have eq15428 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15386 eq8182
    | exact resolve eq8182 eq15386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8182 eq15386
  have eq15441 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq15428
  have eq15481 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6531
       have i₂ := eq15441
       grind)
    | exact superpose eq15441 eq6531
    | exact resolve eq6531 eq15441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6531 eq15441
  have eq15501 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op (M.op x y) (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq15481
  have eq15532 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13377 eq15501
    | exact resolve eq15501 eq13377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13377 eq15501
  have eq15566 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15347 eq15532
    | exact resolve eq15532 eq15347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15347 eq15532
  have eq15567 : x = (M.op x y) := by grind
  clear eq15566
  have eq15583 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq15567
       grind)
    | exact superpose eq15567 eq18
    | exact resolve eq18 eq15567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq15584 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq15567
       grind)
    | exact superpose eq15567 eq22
    | exact resolve eq22 eq15567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq15587 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq15567
       grind)
    | exact superpose eq15567 eq175
    | exact resolve eq175 eq15567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq15588 : ∀ X0 : G, y = (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq15567
       grind)
    | exact superpose eq15567 eq178
    | exact resolve eq178 eq15567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15589 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq186 X0
       have i₂ := eq15567
       grind)
    | exact superpose eq15567 eq186
    | exact resolve eq186 eq15567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq15590 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq211 X0
       have i₂ := eq15567
       grind)
    | exact superpose eq15567 eq211
    | exact resolve eq211 eq15567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq15592 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y (M.op x y)) ∨ (k (M.op x y) y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq703
       have i₂ := eq15567
       grind)
    | exact superpose eq15567 eq703
    | (have r₁ := eq703
       have r₂ := eq15567
       grind)
    | exact resolve eq703 eq15567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq15593 : (k (M.op x y) y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by grind
  clear eq15592
  have eq15594 : y = (M.op x (M.op y (M.op x y))) := by
    first
    | exact superpose eq188 eq15588
    | exact resolve eq15588 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq15588
  have eq15595 : y = (M.op (M.op x y) (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq15594
       have i₂ := eq15567
       grind)
    | exact superpose eq15567 eq15594
    | exact resolve eq15594 eq15567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15594
  have eq15597 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq15584 eq20
    | exact resolve eq20 eq15584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15608 : ∀ X0 : G, (τ (k (σ x) X0)) = (k (M.op x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq15584 eq504
    | exact resolve eq504 eq15584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq15702 : ∀ X0 : G, y = (k (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) ∨ y = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq15583 eq615
    | (have j0 := eq615 y X0 (M.op x y)
       grind)
    | exact resolve eq615 eq15583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq16166 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op (M.op x y) (M.op (M.op y X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq15587 eq180
    | exact resolve eq180 eq15587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16340 : ∀ X0 : G, (M.op y (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq15587 eq15590
    | exact resolve eq15590 eq15587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16385 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op X1 X2)) X0) = (M.op X1 (M.op X2 (M.op (M.op x y) (M.op (M.op x y) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq15590 eq180
    | exact resolve eq180 eq15590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16610 : ∀ X0 : G, (M.op X0 y) ≠ (M.op (M.op x y) (M.op x y)) ∨ (k (M.op X0 y) (M.op X0 y)) = (M.op y (M.op (M.op (M.op x y) (M.op x y)) y)) := by
    intro X0
    first
    | exact superpose eq210 eq185
    | exact resolve eq185 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16627 : ∀ X0 : G, y ≠ (M.op X0 (M.op x y)) ∨ (M.op (M.op x y) (M.op y (M.op x y))) = (k (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq15583 eq185
    | (have j0 := eq185 y X0 x
       grind)
    | exact resolve eq185 eq15583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq16820 : ∀ X0 : G, y = (k (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) ∨ y ≠ (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq15595 eq16627
    | (have j0 := eq16627 X0
       grind)
    | exact resolve eq16627 eq15595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15595 eq16627
  have eq16828 : ∀ X0 : G, (k (M.op X0 y) (M.op X0 y)) = (M.op (M.op x y) (M.op (M.op y (M.op x y)) y)) ∨ (M.op X0 y) ≠ (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16610 X0
       have i₂ := eq3829 y sF0 y sF0
       grind)
    | (have i₁ := eq16610 X0
       have i₂ := eq3829 y y sF0 sF0
       grind)
    | exact superpose eq3829 eq16610
    | (have j0 := eq16610 X0
       grind)
    | exact resolve eq16610 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16610
  have eq16858 : ∀ X0 : G, y = (k (M.op X0 (M.op x y)) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq16820 X0
       have j1 := eq15702 X0
       grind)
    | (have r₁ := eq16820 X0
       have r₂ := eq15702 X0
       grind)
    | exact resolve eq16820 eq15702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15702 eq16820
  have eq16864 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) y)) = (k (M.op X0 y) (M.op X0 y)) ∨ (M.op X0 y) ≠ (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq16166 eq16828
    | (have j0 := eq16828 X0
       grind)
    | exact resolve eq16828 eq16166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16166 eq16828
  have eq16889 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (k (M.op X0 y) (M.op X0 y)) ∨ (M.op X0 y) ≠ (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq15583 eq16864
    | (have j0 := eq16864 X0
       grind)
    | exact resolve eq16864 eq15583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16864
  have eq16901 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (k (M.op X0 y) (M.op X0 y)) := by
    intro X0
    first
    | (have j0 := eq16889 X0
       have j1 := eq7522 X0
       grind)
    | (have r₁ := eq16889 X0
       have r₂ := eq7522 X0
       grind)
    | exact resolve eq16889 eq7522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7522 eq16889
  have eq17220 : (k (M.op x y) (τ (σ y))) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq624 eq15608
    | exact resolve eq15608 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15608
  have eq17268 : (k (M.op x y) y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq17220
    | exact resolve eq17220 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17220
  have eq18422 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq15583 eq16901
    | (have j0 := eq16901 x
       grind)
    | exact resolve eq16901 eq15583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16901
  have eq18443 : y = (M.op y (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq18422 eq210
    | exact resolve eq210 eq18422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18450 : ∀ X0 : G, (M.op y X0) = (M.op (k (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq18422 eq15589
    | exact resolve eq15589 eq18422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15589
  have eq18456 : y = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq18422 eq16858
    | exact resolve eq16858 eq18422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16858
  have eq18462 : ∀ X0 : G, (M.op (k (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq18422 eq16
    | exact resolve eq16 eq18422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18468 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (k (M.op x y) (M.op x y)) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq18422 eq181
    | exact resolve eq181 eq18422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18504 : ∀ X0 : G, (M.op (M.op y y) X0) = (M.op (k (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq18443 eq181
    | exact resolve eq181 eq18443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18524 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y y) X0) := by
    intro X0
    first
    | exact superpose eq18450 eq18504
    | exact resolve eq18504 eq18450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18450 eq18504
  have eq18841 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op y (M.op X0 X1)) (M.op (M.op y y) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X2 (M.op y y) X0 X1
       have i₂ := eq18524 (M.op X0 X1)
       grind)
    | exact superpose eq18524 eq180
    | exact resolve eq180 eq18524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18861 : (σ y) = (M.op (M.op y (σ x)) (M.op (M.op y y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq179 (M.op y y)
       have i₂ := eq18524 sF2
       grind)
    | exact superpose eq18524 eq179
    | exact resolve eq179 eq18524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq18524
  have eq18867 : (σ y) = (M.op y (M.op (M.op (M.op y (σ x)) y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq18861
       have i₂ := eq3829 sF4 y (M.op y sF2) y
       grind)
    | (have i₁ := eq18861
       have i₂ := eq3829 sF4 (M.op y sF2) y y
       grind)
    | exact superpose eq3829 eq18861
    | exact resolve eq18861 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18861
  have eq18874 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op y (M.op (M.op (M.op y (M.op X0 X1)) y) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18841 X0 X1 X2
       have i₂ := eq3829 X2 y (M.op y (M.op X0 X1)) y
       grind)
    | (have i₁ := eq18841 X0 X1 X0
       have i₂ := eq3829 X0 (M.op y (M.op X0 X1)) y y
       grind)
    | exact superpose eq3829 eq18841
    | exact resolve eq18841 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18841
  have eq18901 : (σ y) = (M.op y (M.op (M.op y (M.op y (σ x))) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq18867
       have i₂ := eq3829 sF4 y y (M.op y sF2)
       grind)
    | (have i₁ := eq18867
       have i₂ := eq3829 sF4 y (M.op y sF2) y
       grind)
    | exact superpose eq3829 eq18867
    | exact resolve eq18867 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18867
  have eq18908 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op y (M.op (M.op y (M.op y (M.op X0 X1))) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18874 X0 X1 X2
       have i₂ := eq3829 X2 y y (M.op y (M.op X0 X1))
       grind)
    | (have i₁ := eq18874 X0 X1 X0
       have i₂ := eq3829 X0 y (M.op y (M.op X0 X1)) y
       grind)
    | exact superpose eq3829 eq18874
    | exact resolve eq18874 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18874
  have eq18928 : (σ y) = (M.op y (M.op (M.op (σ x) (M.op y y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq18901
       have i₂ := eq1368 sF2 y y sF4
       grind)
    | (have i₁ := eq18901
       have i₂ := eq1368 y y sF2 sF4
       grind)
    | exact superpose eq1368 eq18901
    | exact resolve eq18901 eq1368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18901
  have eq18930 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op (M.op X1 y) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18908 X0 X1 X2
       have i₂ := eq4870 X0 X1 y y X2
       grind)
    | exact superpose eq4870 eq18908
    | exact resolve eq18908 eq4870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4870 eq18908
  have eq18943 : (σ y) = (M.op (σ x) (M.op (M.op (M.op y y) y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq18928
       have i₂ := eq3829 sF4 (M.op y y) y sF2
       grind)
    | (have i₁ := eq18928
       have i₂ := eq3829 sF4 y sF2 (M.op y y)
       grind)
    | exact superpose eq3829 eq18928
    | exact resolve eq18928 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18928
  have eq18953 : (σ y) = (M.op (σ x) (M.op (M.op y y) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq18943
       have i₂ := eq18930 sF2 (M.op y y) sF4
       grind)
    | exact superpose eq18930 eq18943
    | exact resolve eq18943 eq18930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18943
  have eq18958 : (σ y) = (M.op (σ x) (M.op y (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq18953
       have i₂ := eq18930 sF2 y sF4
       grind)
    | exact superpose eq18930 eq18953
    | exact resolve eq18953 eq18930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18953
  have eq18980 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) y) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq18958 eq177
    | exact resolve eq177 eq18958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18984 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op (M.op y (M.op (σ x) (σ y))) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq18958 eq16
    | exact resolve eq16 eq18958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19010 : ∀ X0 : G, (M.op (σ y) (M.op y (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq4716 eq18984
    | exact resolve eq18984 eq4716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18984
  have eq19013 : ∀ X0 : G, (M.op y (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq18980 X0
       have i₂ := eq3829 (M.op sF3 X0) y sF4 sF2
       grind)
    | (have i₁ := eq18980 X0
       have i₂ := eq3829 (M.op sF3 X0) sF4 sF2 y
       grind)
    | exact superpose eq3829 eq18980
    | exact resolve eq18980 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18980
  have eq19020 : ∀ X0 : G, (M.op (σ x) (M.op (M.op y (M.op (σ x) (σ y))) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq19013 X0
       have i₂ := eq3829 (M.op sF3 X0) sF2 y sF4
       grind)
    | (have i₁ := eq19013 X0
       have i₂ := eq3829 (M.op sF3 X0) y sF4 sF2
       grind)
    | exact superpose eq3829 eq19013
    | exact resolve eq19013 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19013
  have eq19022 : ∀ X0 : G, (M.op y (M.op (σ y) (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq4716 eq19020
    | exact resolve eq19020 eq4716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4716 eq19020
  have eq19225 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op (σ y) y) X0) := by
    intro X0
    first
    | exact superpose eq19010 eq16
    | exact resolve eq16 eq19010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19010
  have eq19456 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ y) X0) X1)) = (M.op X0 (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq19022 eq180
    | exact resolve eq180 eq19022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19457 : ∀ X0 X1 : G, (M.op (M.op (σ y) X0) (M.op (M.op y (σ y)) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq19022 eq177
    | exact resolve eq177 eq19022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19458 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (M.op y (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq19022 eq16
    | exact resolve eq16 eq19022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19461 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op (M.op (σ y) (M.op (σ y) X0)) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq19022 eq16
    | exact resolve eq16 eq19022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19022
  have eq19489 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) (M.op (M.op (M.op (σ y) X0) y) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19461 X0 X0
       have i₂ := eq3829 X0 (M.op sF3 X0) y sF3
       grind)
    | (have i₁ := eq19461 X0 X0
       have i₂ := eq3829 X0 y sF3 (M.op sF3 X0)
       grind)
    | exact superpose eq3829 eq19461
    | exact resolve eq19461 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19461
  have eq19492 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (M.op (σ y) X0) y) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19457 X0 X1
       have i₂ := eq3829 (M.op X0 X1) sF3 (M.op sF3 X0) y
       grind)
    | (have i₁ := eq19457 X0 X1
       have i₂ := eq3829 (M.op X0 X1) (M.op sF3 X0) y sF3
       grind)
    | exact superpose eq3829 eq19457
    | exact resolve eq19457 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19457
  have eq19510 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) (M.op (M.op (σ y) X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19489 X0 x
       have i₂ := eq18930 sF3 (M.op sF3 X0) x
       grind)
    | exact superpose eq18930 eq19489
    | exact resolve eq19489 eq18930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19489
  have eq19513 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ y) X0) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19492 X0 X1
       have i₂ := eq18930 sF3 (M.op sF3 X0) (M.op X0 X1)
       grind)
    | exact superpose eq18930 eq19492
    | exact resolve eq19492 eq18930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19492
  have eq19524 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op y X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq19456 eq19510
    | exact resolve eq19510 eq19456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19510
  have eq19526 : ∀ X0 X1 : G, (M.op X0 (M.op y (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq19456 eq19513
    | exact resolve eq19513 eq19456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19513
  have eq19810 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (σ y) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq19225 eq181
    | exact resolve eq181 eq19225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19225
  have eq20021 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (σ y) (M.op X0 X1)) (M.op (M.op y (σ y)) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq19458 eq180
    | exact resolve eq180 eq19458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19458
  have eq20057 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (σ y) (M.op (M.op (M.op (σ y) (M.op X0 X1)) y) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20021 X0 X1 X0
       have i₂ := eq3829 X0 sF3 (M.op sF3 (M.op X0 X1)) y
       grind)
    | (have i₁ := eq20021 X0 X1 X0
       have i₂ := eq3829 X0 (M.op sF3 (M.op X0 X1)) y sF3
       grind)
    | exact superpose eq3829 eq20021
    | exact resolve eq20021 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3829 eq20021
  have eq20085 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (σ y) (M.op (M.op (σ y) (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20057 X0 X1 X2
       have i₂ := eq18930 sF3 (M.op sF3 (M.op X0 X1)) X2
       grind)
    | exact superpose eq18930 eq20057
    | exact resolve eq20057 eq18930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18930 eq20057
  have eq20104 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X1) (M.op y X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq19456 eq20085
    | exact resolve eq20085 eq19456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19456 eq20085
  have eq20120 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq15590 eq19524
    | exact resolve eq19524 eq15590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15590
  have eq20125 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq18443 eq19524
    | exact resolve eq19524 eq18443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20148 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op y X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19524 (M.op y X1) (M.op X1 X0)
       have i₂ := eq16 X0 y X1
       grind)
    | exact superpose eq16 eq19524
    | exact resolve eq19524 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20227 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X1 (M.op (M.op y X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X2 X1 X1 (M.op y X0)
       have i₂ := eq19524 X1 X0
       grind)
    | exact superpose eq19524 eq180
    | exact resolve eq180 eq19524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20229 : ∀ X0 X1 : G, (M.op y X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op y X0) X1 X1
       have i₂ := eq19524 X1 X0
       grind)
    | exact superpose eq19524 eq16
    | exact resolve eq16 eq19524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19524
  have eq20616 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op (M.op X1 (M.op X2 y)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19526 (M.op X1 X2) (M.op (M.op X1 (M.op X2 y)) X0)
       have i₂ := eq177 y X1 X2 X0
       grind)
    | exact superpose eq177 eq19526
    | exact resolve eq19526 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq20656 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op y (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq180 X2 X1 y (M.op X1 X0)
       have i₂ := eq19526 X1 X0
       grind)
    | exact superpose eq19526 eq180
    | exact resolve eq180 eq19526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20668 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op y (M.op X1 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X2 X1 (M.op y (M.op X1 X0))
       have i₂ := eq19526 X1 X0
       grind)
    | exact superpose eq19526 eq181
    | exact resolve eq181 eq19526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20759 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X1 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20668 X0 X1 X2
       have i₂ := eq20148 X2 (M.op X1 X0)
       grind)
    | exact superpose eq20148 eq20668
    | exact resolve eq20668 eq20148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20668
  have eq21127 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ y) (σ y)) X0) (M.op y (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq19810 eq16
    | exact resolve eq16 eq19810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19810
  have eq21163 : ∀ X0 X1 : G, (M.op (M.op (σ y) (σ y)) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21127 X1 X1
       have i₂ := eq20104 (M.op sF3 sF3) X1 (M.op X1 X1)
       grind)
    | exact superpose eq20104 eq21127
    | exact resolve eq21127 eq20104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21127
  have eq21196 : ∀ X0 X1 : G, (M.op y (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq21163 X0 X1
       have i₂ := eq20229 (M.op X0 (M.op X0 X1)) sF3
       grind)
    | exact superpose eq20229 eq21163
    | exact resolve eq21163 eq20229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20229 eq21163
  have eq21365 : (M.op y y) = (M.op (M.op x y) (M.op (M.op x y) (k (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq15587 (M.op y y)
       have i₂ := eq20125 y
       grind)
    | exact superpose eq20125 eq15587
    | exact resolve eq15587 eq20125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15587
  have eq21616 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op (M.op X0 X1) (M.op y X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X2 (M.op y X0) X1
       have i₂ := eq20148 X1 X0
       grind)
    | exact superpose eq20148 eq181
    | exact resolve eq181 eq20148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20148
  have eq21693 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 (M.op (M.op X0 X1) y)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21616 X0 X1 X2
       have i₂ := eq1368 X0 (M.op X0 X1) y X2
       grind)
    | (have i₁ := eq21616 X2 X1 x
       have i₂ := eq1368 (M.op X2 X1) y X2 x
       grind)
    | exact superpose eq1368 eq21616
    | exact resolve eq21616 eq1368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368 eq21616
  have eq21725 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21693 X0 X1 X2
       have i₂ := eq20616 X2 X0 (M.op X0 X1)
       grind)
    | exact superpose eq20616 eq21693
    | exact resolve eq21693 eq20616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20616 eq21693
  have eq22439 : ∀ X0 : G, (M.op X0 y) = (M.op y (M.op X0 (k (M.op x y) (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq21196 X0 (M.op X0 y)
       have i₂ := eq20125 X0
       grind)
    | exact superpose eq20125 eq21196
    | exact resolve eq21196 eq20125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20125
  have eq22476 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op y (M.op (M.op X0 x) y)) := by
    intro X0
    first
    | exact superpose eq178 eq21196
    | exact resolve eq21196 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq21196
  have eq22768 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq22476 X0
       have i₂ := eq20656 x X0 y
       grind)
    | exact superpose eq20656 eq22476
    | exact resolve eq22476 eq20656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22476
  have eq22807 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq22768 X0
       have i₂ := eq15567
       grind)
    | exact superpose eq15567 eq22768
    | exact resolve eq22768 eq15567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22768
  have eq26237 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op (M.op x y) (M.op y X0)) (M.op y X1)) := by
    intro X0 X1
    first
    | exact superpose eq16340 eq180
    | exact resolve eq180 eq16340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16340
  have eq26280 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op (M.op y X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26237 X0 x
       have i₂ := eq20104 sF0 (M.op y X0) x
       grind)
    | exact superpose eq20104 eq26237
    | exact resolve eq26237 eq20104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20104 eq26237
  have eq26317 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op x y) X1)) = (M.op (M.op x y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq26280 X0 x
       have i₂ := eq20227 X0 sF0 x
       grind)
    | exact superpose eq20227 eq26280
    | exact resolve eq26280 eq20227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26280
  have eq26591 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) X1) = (M.op (M.op X0 (k (M.op x y) (M.op x y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq18462 eq181
    | exact resolve eq181 eq18462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq18462
  have eq26611 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 (k (M.op x y) (M.op x y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26591 X1 x
       have i₂ := eq21725 sF0 X1 x
       grind)
    | exact superpose eq21725 eq26591
    | exact resolve eq26591 eq21725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21725 eq26591
  have eq26742 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op (M.op (k (M.op x y) (M.op x y)) (M.op x y)) (M.op X1 X2)) (M.op (M.op x y) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq18468 eq180
    | exact resolve eq180 eq18468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq18468
  have eq26868 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op X2 (M.op (k (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op (M.op x y) X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26742 X0 X1 X2
       have i₂ := eq4578 (M.op sF0 X0) X1 X2 (k sF0 sF0) sF0
       grind)
    | exact superpose eq4578 eq26742
    | exact resolve eq26742 eq4578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4578 eq26742
  have eq26942 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X1 (M.op (M.op y (M.op X2 (k (M.op x y) (M.op x y)))) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq16385 eq26868
    | exact resolve eq26868 eq16385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16385 eq26868
  have eq26996 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X2 (k (M.op x y) (M.op x y))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq26942 X2 X1 X2
       have i₂ := eq20227 (M.op X2 (k sF0 sF0)) X1 X2
       grind)
    | exact superpose eq20227 eq26942
    | exact resolve eq26942 eq20227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26942
  have eq27025 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op X2 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq26611 eq26996
    | exact resolve eq26996 eq26611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26996
  have eq27079 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op x y))) = (M.op X0 (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq18422 eq26317
    | exact resolve eq26317 eq18422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26317
  have eq27669 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 (k (M.op x y) (M.op x y))) X1) ∨ (M.op X0 X1) = (M.op X0 (k (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq26611 eq28
    | exact resolve eq28 eq26611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28431 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (σ x) (M.op X0 (M.op y (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq18958 eq27025
    | exact resolve eq27025 eq18958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18958
  have eq33514 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) = (M.op X0 (M.op y (σ y))) := by
    intro X0
    first
    | exact superpose eq1413 eq19526
    | exact resolve eq19526 eq1413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1413 eq19526
  have eq38318 : ∀ X0 : G, (M.op (M.op x y) (M.op (M.op x y) (k (M.op x y) (M.op x y)))) = (M.op X0 (M.op (M.op x y) (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq27079 eq20120
    | exact resolve eq20120 eq27079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20120 eq27079
  have eq39091 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op (M.op x y) (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq21365 eq38318
    | exact resolve eq38318 eq21365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21365 eq38318
  have eq44301 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op X2 (M.op (M.op X1 X0) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq27025 X3 X2 (M.op X1 X0)
       have i₂ := eq20759 X1 X0 (M.op X2 X3)
       grind)
    | (have i₁ := eq27025 X3 X2 (M.op X1 X0)
       have i₂ := eq20759 X0 X1 (M.op X2 X3)
       grind)
    | exact superpose eq20759 eq27025
    | exact resolve eq27025 eq20759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20759 eq27025
  have eq47416 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (M.op y (M.op (σ x) (σ y)))) (M.op y (σ y))) := by
    intro X0
    first
    | exact superpose eq28431 eq33514
    | exact resolve eq33514 eq28431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28431 eq33514
  have eq47602 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op y (M.op (M.op (M.op y (M.op (σ x) (σ y))) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq47416 X0
       have i₂ := eq44301 X0 (M.op y sF4) y sF3
       grind)
    | exact superpose eq44301 eq47416
    | exact resolve eq47416 eq44301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44301 eq47416
  have eq47661 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op y (M.op (σ x) (σ y))) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq47602 X0
       have i₂ := eq20656 X0 (M.op y sF4) sF3
       grind)
    | exact superpose eq20656 eq47602
    | exact resolve eq47602 eq20656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20656 eq47602
  have eq47706 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq47661 x
       have i₂ := eq20227 sF4 x sF3
       grind)
    | exact superpose eq20227 eq47661
    | exact resolve eq47661 eq20227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20227 eq47661
  have eq60399 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) ∨ (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (k (M.op (σ x) (σ y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq47706 eq13
    | (have j0 := eq13 (M.op (σ x) (σ y)) (M.op X0 (σ y))
       grind)
    | exact resolve eq13 eq47706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47706
  have eq60455 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (σ y))) = (k (M.op (σ x) (σ y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | (have j0 := eq60399 X0
       have j1 := eq28 (M.op (σ x) (σ y)) (M.op X0 (σ y))
       grind)
    | (have r₁ := eq60399 X0
       have r₂ := eq28 (M.op (σ x) (σ y)) (M.op X0 (σ y))
       grind)
    | exact resolve eq60399 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq60399
  have eq60662 : ∀ X0 : G, (M.op X0 y) ≠ (M.op X0 (k (M.op x y) (M.op x y))) ∨ (M.op (M.op X0 (k (M.op x y) (M.op x y))) y) = (k (M.op X0 (k (M.op x y) (M.op x y))) y) := by
    intro X0
    first
    | exact superpose eq22439 eq13
    | (have j0 := eq13 (M.op X0 (k (M.op x y) (M.op x y))) y
       grind)
    | exact resolve eq13 eq22439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22439
  have eq60727 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 (k (M.op x y) (M.op x y))) y) ∨ (M.op X0 y) ≠ (M.op X0 (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq26611 eq60662
    | (have j0 := eq60662 X0
       grind)
    | exact resolve eq60662 eq26611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26611 eq60662
  have eq60808 : ∀ X0 : G, (M.op X0 y) = (k (M.op X0 (k (M.op x y) (M.op x y))) y) := by
    intro X0
    first
    | (have j0 := eq60727 X0
       have j1 := eq27669 X0 y
       grind)
    | (have r₁ := eq60727 X0
       have r₂ := eq27669 X0 y
       grind)
    | exact resolve eq60727 eq27669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27669 eq60727
  have eq69780 : (σ y) = (M.op (σ y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq60455 eq240
    | exact resolve eq240 eq60455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq60455
  have eq69908 : (σ y) = (M.op (σ y) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq69780
    | exact resolve eq69780 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq69780
  have eq74584 : (k y y) = (M.op y y) := by
    first
    | exact superpose eq18443 eq60808
    | exact resolve eq60808 eq18443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18443 eq60808
  have eq74662 : (M.op y (M.op x y)) = (M.op (M.op x y) (k y y)) := by
    first
    | (have i₁ := eq22807 y
       have i₂ := eq74584
       grind)
    | exact superpose eq74584 eq22807
    | exact resolve eq22807 eq74584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22807
  have eq116585 : (k (M.op x y) y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq15593 eq18422
    | exact resolve eq18422 eq15593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15593 eq18422
  have eq117431 : (k (σ (M.op x y)) (σ y)) = (σ (k (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq116585 eq41
    | exact resolve eq41 eq116585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq116585
  have eq117438 : (k (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq42 eq117431
    | exact resolve eq117431 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117431
  have eq117441 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq15597 eq117438
    | exact resolve eq117438 eq15597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117438
  have eq117444 : (k (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq20 eq117441
    | exact resolve eq117441 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117441
  have eq117447 : (k (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq15597 eq117444
    | exact resolve eq117444 eq15597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117444
  have eq117455 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq117447 eq624
    | exact resolve eq624 eq117447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624 eq117447
  have eq316831 : ∀ X0 : G, (σ (k X0 (k x (M.op x y)))) = (k (σ X0) (k (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq15584 eq43
    | exact resolve eq43 eq15584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq15584
  have eq316847 : ∀ X0 : G, (σ (k X0 (k (M.op x y) (M.op x y)))) = (k (σ X0) (k (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq316831 X0
       have i₂ := eq15567
       grind)
    | exact superpose eq15567 eq316831
    | exact resolve eq316831 eq15567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15567 eq316831
  have eq316974 : (σ y) = (k (σ (k (M.op x y) (M.op x y))) (k (σ x) (σ x))) := by
    first
    | exact superpose eq18456 eq316847
    | exact resolve eq316847 eq18456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18456 eq316847
  have eq317025 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ x) (σ x))) := by
    first
    | exact superpose eq42 eq316974
    | exact resolve eq316974 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq316974
  have eq317045 : (σ y) = (k (k (σ (M.op x y)) (σ x)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq15597 eq317025
    | exact resolve eq317025 eq15597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317025
  have eq317062 : (σ y) = (k (k (σ (M.op x y)) (σ x)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq20 eq317045
    | exact resolve eq317045 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317045
  have eq317070 : (σ y) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq15597 eq317062
    | exact resolve eq317062 eq15597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317062
  have eq317071 : (σ y) = (k (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq317070
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq317070
    | exact resolve eq317070 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq317070
  have eq317072 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq117455 eq317071
    | exact resolve eq317071 eq117455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117455 eq317071
  have eq317216 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq317072 eq69908
    | exact resolve eq69908 eq317072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69908 eq317072
  have eq654256 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq317216 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq317216
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq317216
       grind)
    | exact resolve eq13 eq317216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317216
  have eq654334 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by grind
  clear eq654256
  have eq685747 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq654334 eq153
    | exact resolve eq153 eq654334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq654334
  have eq685758 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq32 eq685747
    | exact resolve eq685747 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq685747
  have eq700669 : (M.op y (M.op (M.op x y) (M.op x y))) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq685758 eq39091
    | exact resolve eq39091 eq685758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39091 eq685758
  have eq700829 : (k y y) = (M.op y (M.op (M.op x y) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | (have i₁ := eq700669
       have i₂ := eq74584
       grind)
    | exact superpose eq74584 eq700669
    | exact resolve eq700669 eq74584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74584 eq700669
  have eq700891 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) := by
    first
    | exact superpose eq210 eq700829
    | exact resolve eq700829 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq700829
  have eq700892 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq700891
  have eq700934 : (M.op y (M.op x y)) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq74662
       have i₂ := eq700892
       grind)
    | exact superpose eq700892 eq74662
    | exact resolve eq74662 eq700892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74662 eq700892
  have eq700971 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15583 eq700934
    | exact resolve eq700934 eq15583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700934
  have eq701165 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq700971 eq13
    | (have j0 := eq13 (M.op x y) y
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq700971
       grind)
    | exact resolve eq13 eq700971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700971
  have eq701247 : (k (M.op x y) y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq701165
  have eq701283 : (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15583 eq701247
    | exact resolve eq701247 eq15583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15583 eq701247
  have eq702065 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq701283 eq17268
    | exact resolve eq17268 eq701283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17268 eq701283
  have eq702076 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq702065
  have eq702095 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq702076 eq14
    | exact resolve eq14 eq702076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702076
  have eq702096 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq702095
    | exact resolve eq702095 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq702095
  have eq702099 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq702096
       have r₂ := eq27
       grind)
    | exact resolve eq702096 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702096
  have eq702102 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq702099 eq27
    | exact resolve eq27 eq702099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq702099
  have eq702457 : False := by grind
  exact eq702457

/-- `Equation1590`: `x = (y ◇ z) ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxx_pyx_pxy_pxx_pyx_Equation1590 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1590 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1590.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X0) = X1 := by
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
  clear eq23
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X1 X0)) (M.op (M.op X1 X2) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X1 X2) (M.op X2 (M.op X1 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X0)) = (M.op (M.op (M.op X1 X2) X3) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X1 X0)) (M.op X1 X2) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 (M.op X2 X1)
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) X3) = (M.op (M.op (M.op X2 (M.op X1 X0)) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq64 X3 (M.op X2 (M.op X1 X0)) (M.op X1 X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (M.op X0 X1)
       have i₂ := eq64 (M.op (M.op X0 X1) (M.op X1 X2)) X1 X0
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X1) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 X1 (M.op X0 X1) X2
       have i₂ := eq64 (M.op (M.op X0 X1) X2) X1 X0
       grind)
    | exact superpose eq64 eq71
    | exact resolve eq71 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op X1 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X2 (M.op X1 X0) (M.op (M.op X1 X0) X1)
       have i₂ := eq71 (M.op X1 X0) X1 X0
       grind)
    | exact superpose eq71 eq64
    | exact resolve eq64 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) X3) = (M.op (M.op X0 (M.op X2 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq89 (M.op X1 (M.op X2 X0)) (M.op X2 X1) X3
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq89
    | exact resolve eq89 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X3) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq89 (M.op (M.op X1 X2) (M.op X2 X0)) X1 X3
       have i₂ := eq71 X1 X2 X0
       grind)
    | exact superpose eq71 eq89
    | exact resolve eq89 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X1 (M.op (M.op X2 (M.op X3 X1)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X1 X3 X2 (M.op X2 (M.op X3 X0))
       have i₂ := eq9 X0 X3 X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq257 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X1 X0) X4)) = (M.op (M.op X0 (M.op X1 X2)) (M.op (M.op X3 X2) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 X4 (M.op X1 X0) X3 (M.op X3 X2)
       have i₂ := eq63 X2 X1 X0 X3
       grind)
    | exact superpose eq63 eq63
    | exact resolve eq63 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 (M.op X4 X0)))) = (M.op (M.op (M.op X2 X1) (M.op X4 X3)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 (M.op X3 (M.op X4 X0)) X2 X1 (M.op X4 X3)
       have i₂ := eq9 X0 X4 X3
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 (M.op (M.op X3 X4) X0)))) = (M.op (M.op (M.op X2 X1) X4) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq63 (M.op X3 (M.op (M.op X3 X4) X0)) X2 X1 X4
       have i₂ := eq86 X3 X4 X0
       grind)
    | exact superpose eq86 eq63
    | exact resolve eq63 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq291 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op X2 (M.op X1 (M.op X0 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq124 X0 X1 X2 X3
       have i₂ := eq260 X3 X2 X1 X0 X2
       grind)
    | exact superpose eq260 eq124
    | exact resolve eq124 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq447 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 X0) X3) X4) X5) = (M.op (M.op (M.op X4 (M.op X0 (M.op X1 X2))) (M.op X3 X2)) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq67 (M.op X3 X2) (M.op (M.op X1 X0) X3) X4 X5
       have i₂ := eq63 X2 X1 X0 X3
       grind)
    | exact superpose eq63 eq67
    | exact resolve eq67 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 X0) X3) X4) X5) = (M.op (M.op X2 (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2))))) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq447 X0 X1 X2 X3 X4 X5
       have i₂ := eq121 X2 (M.op X4 (M.op X0 (M.op X1 X2))) X3 X5
       grind)
    | (have i₁ := eq447 X0 X1 X2 X3 X4 X5
       have i₂ := eq121 (M.op X4 (M.op X0 (M.op X1 X2))) X2 X3 X5
       grind)
    | exact superpose eq121 eq447
    | exact resolve eq447 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq541 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op (M.op X1 X0) X4) X5)) = (M.op (M.op X4 X2) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq181 X5 (M.op X4 X2) X3 (M.op (M.op X1 X0) X4)
       have i₂ := eq63 X2 X1 X0 X4
       grind)
    | exact superpose eq63 eq181
    | exact resolve eq181 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 X1)) = (M.op (M.op (M.op X2 X3) X0) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq181 X1 X3 (M.op (M.op X2 X3) X0) X2
       have i₂ := eq89 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq89 eq181
    | exact resolve eq181 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X3)) X2) = (M.op (M.op X3 X4) (M.op X4 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op (M.op X0 (M.op X1 X3)) X2) X3 X4
       have i₂ := eq181 X2 X3 X0 X1
       grind)
    | exact superpose eq181 eq9
    | exact resolve eq9 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq577 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X4)) X2) = (M.op X3 (M.op (M.op X3 X4) (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq71 X3 X4 (M.op (M.op X0 (M.op X1 X4)) X2)
       have i₂ := eq181 X2 X4 X0 X1
       grind)
    | exact superpose eq181 eq71
    | exact resolve eq71 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 (M.op X0 (M.op X1 X2)))) = (M.op (M.op X0 (M.op X1 (M.op X4 X3))) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq86 X4 X3 (M.op (M.op X0 (M.op X1 (M.op X4 X3))) X2)
       have i₂ := eq181 X2 (M.op X4 X3) X0 X1
       grind)
    | exact superpose eq181 eq86
    | exact resolve eq86 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq181
  have eq589 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 X0) X3) X4) X5) = (M.op (M.op X0 (M.op X1 X2)) (M.op X4 (M.op X2 (M.op X3 X5)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq517 X0 X1 X2 X3 X4 X5
       have i₂ := eq583 X2 X3 X5 (M.op X0 (M.op X1 X2)) X4
       grind)
    | exact superpose eq583 eq517
    | exact resolve eq517 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq622 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op (M.op X1 X0) X4) X5)) = (M.op (M.op X4 X2) (M.op X2 (M.op X1 (M.op X3 (M.op X0 X5))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq541 X0 X1 X2 X3 X4 X5
       have i₂ := eq583 X3 X0 X5 X2 X1
       grind)
    | exact superpose eq583 eq541
    | exact resolve eq541 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq638 : ∀ X0 X1 X3 X4 X5 : G, (M.op X3 (M.op (M.op (M.op X1 X0) X4) X5)) = (M.op (M.op X1 (M.op X3 X4)) (M.op X0 X5)) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq622 X0 X1 x X3 X4 X5
       have i₂ := eq572 X1 X3 (M.op X0 X5) X4 x
       grind)
    | exact superpose eq572 eq622
    | exact resolve eq622 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq622
  have eq649 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op (M.op X1 X0) X4)) = (M.op X1 (M.op (M.op (M.op X0 (M.op X3 X2)) X2) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq257 X0 X1 X2 X3 X4
       have i₂ := eq638 (M.op X3 X2) X0 X1 X2 X4
       grind)
    | exact superpose eq638 eq257
    | exact resolve eq257 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq650 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 X0) X3) X4) X5) = (M.op X1 (M.op (M.op (M.op X0 X4) X2) (M.op X2 (M.op X3 X5)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq589 X0 X1 X2 X3 X4 X5
       have i₂ := eq638 X4 X0 X1 X2 (M.op X2 (M.op X3 X5))
       grind)
    | exact superpose eq638 eq589
    | exact resolve eq589 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589 eq638
  have eq654 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X1 X0) X3) X4) X5) = (M.op X1 (M.op X4 (M.op X0 (M.op X3 X5)))) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq650 X0 X1 x X3 X4 X5
       have i₂ := eq63 (M.op X3 X5) X0 X4 x
       grind)
    | exact superpose eq63 eq650
    | exact resolve eq650 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq650
  have eq655 : ∀ X0 X1 X3 X4 : G, (M.op X3 (M.op (M.op X1 X0) X4)) = (M.op X1 (M.op (M.op X3 X0) X4)) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq649 X0 X1 x X3 X4
       have i₂ := eq67 x X3 X0 X4
       grind)
    | exact superpose eq67 eq649
    | exact resolve eq649 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq751 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X2) X1) X4) = (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X3)) X3) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq67 X3 (M.op X0 X2) X1 X4
       have i₂ := eq655 X2 X0 X1 X3
       grind)
    | (have i₁ := eq67 X3 (M.op X0 X2) X1 X4
       have i₂ := eq655 X2 X1 X0 X3
       grind)
    | exact superpose eq655 eq67
    | exact resolve eq67 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq804 : ∀ X0 X1 X2 X4 : G, (M.op (M.op (M.op X0 X2) X1) X4) = (M.op (M.op (M.op X1 X2) X0) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq751 X0 X1 X2 x X4
       have i₂ := eq67 x (M.op X1 X2) X0 X4
       grind)
    | exact superpose eq67 eq751
    | exact resolve eq751 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq751
  have eq2771 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2827 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X1 (M.op X0 X1)) X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X2 X1 X1
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq64 X0 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq64
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2878 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2771 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2771
  have eq2879 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2878 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2878
  have eq2897 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X0 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2827 X0 X1 X2
       have i₂ := eq64 X2 X1 X0
       grind)
    | exact superpose eq64 eq2827
    | (have j0 := eq2827 X0 X1 X2
       grind)
    | exact resolve eq2827 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2827
  have eq3061 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X4 X3) (M.op (M.op X2 X1) X0)) X5) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X3) X4) X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq804 X4 (M.op (M.op X2 X1) X0) X3 X5
       have i₂ := eq804 X2 X0 X1 X3
       grind)
    | (have i₁ := eq804 X4 (M.op (M.op X2 X1) X0) X3 X5
       have i₂ := eq804 X0 X2 X1 X3
       grind)
    | exact superpose eq804 eq804
    | exact resolve eq804 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3376 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X4 X3) (M.op (M.op X2 X1) X0)) X5) = (M.op (M.op X0 X1) (M.op X4 (M.op X2 (M.op X3 X5)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3061 X0 X1 X2 X3 X4 X5
       have i₂ := eq654 X2 (M.op X0 X1) X3 X4 X5
       grind)
    | exact superpose eq654 eq3061
    | exact resolve eq3061 eq654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq3061
  have eq3520 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X4 (M.op X2 (M.op X3 X5)))) = (M.op X3 (M.op X4 (M.op X0 (M.op (M.op X2 X1) X5)))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3376 X0 X1 X2 X3 X4 X5
       have i₂ := eq260 X5 X3 X4 X0 (M.op X2 X1)
       grind)
    | exact superpose eq260 eq3376
    | exact resolve eq3376 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3376
  have eq7502 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq2879 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2879
  have eq7505 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7502 X0 X1
       have j1 := eq2897 X1 X0 x
       grind)
    | (have r₁ := eq7502 X0 X1
       have r₂ := eq2897 X0 X1 X0
       grind)
    | (have r₁ := eq7502 X1 X0
       have r₂ := eq2897 X0 X1 X1
       grind)
    | (have r₁ := eq7502 X1 X1
       have r₂ := eq2897 (M.op X1 X1) X1 x
       grind)
    | exact resolve eq7502 eq2897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2897 eq7502
  have eq7696 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  have eq7840 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq7696 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7696
  have eq7902 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7840 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7840
  have eq8043 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq7902 (σ X0)
       grind)
    | exact superpose eq7902 eq15
    | exact resolve eq15 eq7902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8045 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq7902 (τ X0)
       grind)
    | exact superpose eq7902 eq32
    | exact resolve eq32 eq7902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8060 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8045 X0
       have i₂ := eq7902 X0
       grind)
    | exact superpose eq7902 eq8045
    | exact resolve eq8045 eq7902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8045
  have eq8062 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8043 X0
       have i₂ := eq7902 X0
       grind)
    | exact superpose eq7902 eq8043
    | exact resolve eq8043 eq7902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7902 eq8043
  have eq8402 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op (τ X0) X1) (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (τ X0) (τ X0) X1
       have i₂ := eq8060 X0
       grind)
    | exact superpose eq8060 eq9
    | exact resolve eq9 eq8060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8406 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (M.op (τ X0) (τ (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 (τ X0) (τ X0)
       have i₂ := eq8060 X0
       grind)
    | exact superpose eq8060 eq64
    | exact resolve eq64 eq8060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8408 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X1 (τ X0) (τ X0)
       have i₂ := eq8060 X0
       grind)
    | exact superpose eq8060 eq71
    | exact resolve eq71 eq8060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8409 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ (M.op X0 X0)) (M.op (τ X0) X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71 (τ X0) (τ X0) X1
       have i₂ := eq8060 X0
       grind)
    | exact superpose eq8060 eq71
    | exact resolve eq71 eq8060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8415 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (M.op (τ (M.op X0 X0)) (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq89 (τ X0) (τ X0) X1
       have i₂ := eq8060 X0
       grind)
    | exact superpose eq8060 eq89
    | exact resolve eq89 eq8060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq8447 : ∀ X0 : G, (k (τ X0) (τ (M.op X0 X0))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    grind
  have eq8451 : ∀ X0 : G, (τ (k X0 (M.op X0 X0))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq8447 X0
       have i₂ := eq32 (M.op X0 X0) X0
       grind)
    | exact superpose eq32 eq8447
    | exact resolve eq8447 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq8447
  have eq8464 : ∀ X0 : G, (τ (M.op X0 (M.op X0 X0))) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq8451
  have eq8475 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op (τ (M.op X0 (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8406 X0 X1
       have i₂ := eq8464 X0
       grind)
    | exact superpose eq8464 eq8406
    | exact resolve eq8406 eq8464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8406
  have eq8495 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (M.op (σ X0) (σ (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X1 (σ X0) (σ X0)
       have i₂ := eq8062 X0
       grind)
    | exact superpose eq8062 eq64
    | exact resolve eq64 eq8062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq8497 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X1 (σ X0) (σ X0)
       have i₂ := eq8062 X0
       grind)
    | exact superpose eq8062 eq71
    | exact resolve eq71 eq8062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq8532 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = X1 ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7505 (σ X0) X1
       have i₂ := eq8062 X0
       grind)
    | exact superpose eq8062 eq7505
    | (have j0 := eq7505 (σ X0) X1
       grind)
    | exact resolve eq7505 eq8062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8536 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq8540 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq8536 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq8536
    | exact resolve eq8536 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8536
  have eq8545 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq8540
  have eq8563 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 (M.op X0 X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8495 X0 X1
       have i₂ := eq8545 X0
       grind)
    | exact superpose eq8545 eq8495
    | exact resolve eq8495 eq8545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8495 eq8545
  have eq9554 : ∀ X0 : G, (τ X0) = (M.op (M.op (τ X0) (τ (M.op X0 X0))) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq8402 X0 (τ (M.op X0 X0))
       have i₂ := eq8060 (M.op X0 X0)
       grind)
    | exact superpose eq8060 eq8402
    | exact resolve eq8402 eq8060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8060
  have eq9636 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (τ X0) X2) X3) = (M.op (M.op (M.op X2 (M.op X1 (τ (M.op X0 X0)))) (M.op (τ X0) X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq804 (M.op (τ X0) X1) X2 (M.op X1 (τ (M.op X0 X0))) X3
       have i₂ := eq8402 X0 X1
       grind)
    | exact superpose eq8402 eq804
    | exact resolve eq804 eq8402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8402
  have eq9639 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (τ X0) X2) X3) = (M.op (M.op X1 (M.op (τ X0) (M.op X2 (M.op X1 (τ (M.op X0 X0)))))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9636 X0 X1 X2 X3
       have i₂ := eq121 X1 (M.op X2 (M.op X1 (τ (M.op X0 X0)))) (τ X0) X3
       grind)
    | (have i₁ := eq9636 X0 X1 X2 X3
       have i₂ := eq121 (M.op X2 (M.op X1 (τ (M.op X0 X0)))) X1 (τ X0) X3
       grind)
    | exact superpose eq121 eq9636
    | exact resolve eq9636 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq9636
  have eq9694 : ∀ X0 : G, (τ X0) = (M.op (τ (M.op X0 (M.op X0 X0))) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9554 X0
       have i₂ := eq8464 X0
       grind)
    | exact superpose eq8464 eq9554
    | exact resolve eq9554 eq8464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8464 eq9554
  have eq9740 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (τ X0) X2) X3) = (M.op (M.op X1 (τ (M.op X0 X0))) (M.op X2 (M.op X1 (M.op (τ X0) X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9639 X0 X1 X2 X3
       have i₂ := eq583 X1 (τ X0) X3 (M.op X1 (τ (M.op X0 X0))) X2
       grind)
    | exact superpose eq583 eq9639
    | exact resolve eq9639 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq9639
  have eq9753 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq9694 X0
       have i₂ := eq8475 X0 (τ (M.op (M.op X0 X0) (M.op X0 X0)))
       grind)
    | exact superpose eq8475 eq9694
    | exact resolve eq9694 eq8475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8475 eq9694
  have eq9785 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (τ X0) X2) X3) = (M.op (τ X0) (M.op X2 (M.op X1 (M.op (M.op X1 (τ (M.op X0 X0))) X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9740 X0 X1 X2 X3
       have i₂ := eq3520 X1 (τ (M.op X0 X0)) X1 (τ X0) X2 X3
       grind)
    | exact superpose eq3520 eq9740
    | exact resolve eq9740 eq3520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3520 eq9740
  have eq9803 : ∀ X0 X2 X3 : G, (M.op (M.op (τ X0) X2) X3) = (M.op (M.op (M.op X2 (τ X0)) (τ (M.op X0 X0))) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq9785 X0 x X2 X3
       have i₂ := eq265 X3 (τ X0) X2 x (τ (M.op X0 X0))
       grind)
    | exact superpose eq265 eq9785
    | exact resolve eq9785 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq9785
  have eq10176 : ∀ X0 X1 : G, (M.op (M.op (τ X1) (τ X0)) (τ (M.op X0 X0))) = (M.op (τ X1) (M.op (τ (M.op X1 X1)) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq8409 X1 (M.op (M.op (τ X1) (τ X0)) (τ (M.op X0 X0)))
       have i₂ := eq8408 X0 (τ X1)
       grind)
    | exact superpose eq8408 eq8409
    | exact resolve eq8409 eq8408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8409
  have eq10695 : ∀ X0 X1 : G, (M.op (σ (M.op (τ (M.op X0 X0)) (τ X0))) X1) = (M.op (σ (M.op (M.op (τ (M.op X0 X0)) (τ X0)) (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ X0))))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8563 (M.op (τ (M.op X0 X0)) (τ X0)) X1
       have i₂ := eq8415 X0 (M.op (τ (M.op X0 X0)) (τ X0))
       grind)
    | exact superpose eq8415 eq8563
    | exact resolve eq8563 eq8415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8563
  have eq10833 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = (M.op (σ (M.op (τ (M.op X0 X0)) (τ X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10695 X0 X1
       have i₂ := eq9 (τ X0) (τ (M.op X0 X0)) (τ X0)
       grind)
    | exact superpose eq9 eq10695
    | exact resolve eq10695 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10695
  have eq10897 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (σ (M.op (τ (M.op X0 X0)) (τ X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10833 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10833
    | exact resolve eq10833 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10833
  have eq12077 : ∀ X0 X1 : G, (σ (M.op (τ (M.op X0 X0)) (τ X0))) = (M.op X1 (M.op (M.op X1 (σ (M.op (τ (M.op X0 X0)) (τ X0)))) (σ (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq8497 (M.op (τ (M.op X0 X0)) (τ X0)) X1
       have i₂ := eq8415 X0 (M.op (τ (M.op X0 X0)) (τ X0))
       grind)
    | exact superpose eq8415 eq8497
    | exact resolve eq8497 eq8415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8415 eq8497
  have eq13845 : ∀ X0 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (τ X0) (M.op (τ X0) (τ (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0)))))) := by
    intro X0
    first
    | (have i₁ := eq8408 (M.op (M.op X0 X0) (M.op X0 X0)) (τ X0)
       have i₂ := eq9753 X0
       grind)
    | exact superpose eq9753 eq8408
    | exact resolve eq8408 eq9753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8408
  have eq13876 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (τ (M.op (M.op X0 X0) (M.op X0 X0))))) = (M.op (M.op (M.op (τ X0) X1) X2) (τ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq555 X2 (τ (M.op (M.op X0 X0) (M.op X0 X0))) (τ X0) X1
       have i₂ := eq9753 X0
       grind)
    | exact superpose eq9753 eq555
    | exact resolve eq555 eq9753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555 eq9753
  have eq13895 : ∀ X0 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op (τ (M.op X0 X0)) (τ X0)) (τ X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq13845 X0
       have i₂ := eq13876 (M.op X0 X0) (τ X0) (τ X0)
       grind)
    | exact superpose eq13876 eq13845
    | exact resolve eq13845 eq13876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13845 eq13876
  have eq13961 : ∀ X0 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (M.op (τ X0) (τ X0)) (τ (M.op X0 X0))) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq13895 X0
       have i₂ := eq804 (τ (M.op X0 X0)) (τ X0) (τ X0) (τ (M.op X0 X0))
       grind)
    | (have i₁ := eq13895 X0
       have i₂ := eq804 (τ X0) (τ (M.op X0 X0)) (τ X0) (τ (M.op X0 X0))
       grind)
    | exact superpose eq804 eq13895
    | exact resolve eq13895 eq804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804 eq13895
  have eq14001 : ∀ X0 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (M.op (τ X0) (τ X0)) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq13961 X0
       have i₂ := eq9803 X0 (τ X0) (τ (M.op X0 X0))
       grind)
    | exact superpose eq9803 eq13961
    | exact resolve eq13961 eq9803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9803 eq13961
  have eq14031 : ∀ X0 : G, (τ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq14001 X0
       have i₂ := eq10176 X0 X0
       grind)
    | exact superpose eq10176 eq14001
    | exact resolve eq14001 eq10176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10176 eq14001
  have eq14063 : ∀ X0 X1 : G, (σ (M.op (τ (M.op X0 X0)) (τ X0))) = (M.op X1 (M.op (M.op X1 (σ (M.op (τ (M.op X0 X0)) (τ X0)))) (σ (τ (M.op (M.op X0 X0) (M.op X0 X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq12077 X0 X1
       have i₂ := eq14031 X0
       grind)
    | exact superpose eq14031 eq12077
    | exact resolve eq12077 eq14031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12077 eq14031
  have eq14090 : ∀ X0 X1 : G, (σ (M.op (τ (M.op X0 X0)) (τ X0))) = (M.op X1 (M.op (M.op X1 (σ (M.op (τ (M.op X0 X0)) (τ X0)))) (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14063 X0 X1
       have i₂ := eq11 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq11 eq14063
    | exact resolve eq14063 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14063
  have eq14111 : ∀ X0 : G, (σ (M.op (τ (M.op X0 X0)) (τ X0))) = (M.op (M.op (M.op X0 X0) (M.op X0 (σ (M.op (τ (M.op X0 X0)) (τ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq14090 X0 x
       have i₂ := eq577 (M.op X0 X0) X0 X0 x (σ (M.op (τ (M.op X0 X0)) (τ X0)))
       grind)
    | exact superpose eq577 eq14090
    | exact resolve eq14090 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577 eq14090
  have eq14127 : ∀ X0 : G, (σ (M.op (τ (M.op X0 X0)) (τ X0))) = (M.op X0 (M.op X0 (M.op (σ (M.op (τ (M.op X0 X0)) (τ X0))) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq14111 X0
       have i₂ := eq260 X0 X0 X0 (σ (M.op (τ (M.op X0 X0)) (τ X0))) X0
       grind)
    | exact superpose eq260 eq14111
    | exact resolve eq14111 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260 eq14111
  have eq14137 : ∀ X0 : G, (σ (M.op (τ (M.op X0 X0)) (τ X0))) = (M.op (M.op (σ (M.op (τ (M.op X0 X0)) (τ X0))) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq14127 X0
       have i₂ := eq291 (σ (M.op (τ (M.op X0 X0)) (τ X0))) X0 X0 X0
       grind)
    | exact superpose eq291 eq14127
    | exact resolve eq14127 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291 eq14127
  have eq14145 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq14137 X0
       have i₂ := eq10897 X0 X0
       grind)
    | exact superpose eq10897 eq14137
    | exact resolve eq14137 eq10897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10897 eq14137
  have eq14880 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (τ (M.op (σ X0) (σ X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq14145 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14145
    | exact resolve eq14145 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14145
  have eq14926 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (τ (σ (M.op X0 X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq14880 X0
       have i₂ := eq8062 X0
       grind)
    | exact superpose eq8062 eq14880
    | exact resolve eq14880 eq8062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8062 eq14880
  have eq14965 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq14926 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq14926
    | exact resolve eq14926 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14926
  have eq20149 : ∀ X0 X1 : G, (τ X0) = (M.op X1 X1) ∨ (k (σ X1) X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq8532 X1 X0
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq8532 X0 (σ X0)
       grind)
    | exact superpose eq8532 eq10
    | (have j1 := eq8532 X1 X0
       grind)
    | exact resolve eq10 eq8532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8532
  have eq23039 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (τ (σ X0)) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq20149 (σ X0) X1
       grind)
    | exact superpose eq20149 eq15
    | (have j1 := eq20149 (σ X0) X1
       grind)
    | exact resolve eq15 eq20149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20149
  have eq23057 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23039 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq23039
    | (have j0 := eq23039 X0 X1
       grind)
    | exact resolve eq23039 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23039
  have eq25004 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23057 X0 X1
       have i₂ := eq7505 X1 X0
       grind)
    | exact superpose eq7505 eq23057
    | (have j0 := eq23057 X0 X1
       have j1 := eq7505 X1 X0
       grind)
    | exact resolve eq23057 eq7505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7505 eq23057
  have eq25216 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq25004 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25004
  have eq26420 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14965 X1
       have i₂ := eq25216 X0 X1
       grind)
    | (have i₁ := eq14965 X0
       have i₂ := eq25216 (M.op X0 X0) X1
       grind)
    | exact superpose eq25216 eq14965
    | (have j1 := eq25216 X0 X1
       grind)
    | exact resolve eq14965 eq25216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14965 eq25216
  have eq26562 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq26420 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26420
  have eq27018 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26562 x y
       grind)
    | exact superpose eq26562 eq16
    | (have r₁ := eq16
       have r₂ := eq26562 x y
       grind)
    | exact resolve eq16 eq26562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26562
  have eq27020 : False := by grind
  exact eq27020

/-- `Equation1590`: `x = (y ◇ z) ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_pyy_pyx_pyx_pxy_Equation1590 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1590 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1590.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
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
  have eq31 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 x X0
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq10 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10
    | (have j0 := eq10 x
       grind)
    | exact resolve eq10 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 y
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq49 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq52 : ∀ X0 : G, (M.op (M.op x y) (M.op y (M.op x X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 X0 x y
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X1 X0)) (M.op (M.op X1 X2) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op X1 X2) (M.op X2 (M.op X1 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq9
    | (have j0 := eq9 y x X0
       grind)
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X0)) = (M.op (M.op (M.op X1 X2) X3) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X1 X0)) (M.op X1 X2) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X2 X0) X1 (M.op X2 X1)
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) X0) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 (σ y) (σ x) X0
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 X0 (σ x) (σ y)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq31 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31
    | (have j0 := eq31 y
       grind)
    | exact resolve eq31 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq79 : y = (M.op (M.op x y) (M.op y (M.op x y))) := by
    first
    | (have i₁ := eq52 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (M.op y (M.op (M.op y (M.op x y)) (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq79 eq9
    | exact resolve eq9 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 : G, (M.op y (M.op x (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq80 eq85
    | exact resolve eq85 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq92 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 (M.op x y)) (M.op (M.op x X0) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq57
    | (have j0 := eq57 (σ y)
       grind)
    | exact resolve eq57 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (M.op (σ x) X0) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq57 eq9
    | exact resolve eq9 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq95 eq9
    | exact resolve eq9 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq126 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq127 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq126 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq126 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq126 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq137 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq127 (σ X0)
       grind)
    | exact superpose eq127 eq15
    | exact resolve eq15 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq138 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq137 X0
       have i₂ := eq127 X0
       grind)
    | exact superpose eq127 eq137
    | exact resolve eq137 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq144 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq58 eq9
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq151 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq144 eq103
    | exact resolve eq103 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq156 : ∀ X0 : G, (M.op x (M.op (M.op x y) (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq80 eq9
    | exact resolve eq9 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : y = (M.op (M.op x (M.op y (M.op x y))) (M.op x (M.op x y))) := by
    first
    | exact superpose eq80 eq54
    | exact resolve eq54 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq164 : (σ y) = (M.op (M.op (σ x) (M.op y (M.op x y))) (M.op x (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq80 eq57
    | exact resolve eq57 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq173 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) ≠ (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) = X0 ∨ (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) = (k X0 (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq144 eq13
    | (have j0 := eq13 X0 (M.op (σ y) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq13 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (σ x) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq144 eq9
    | exact resolve eq9 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) ≠ (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) = (k X0 (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq173 X0
       have j1 := eq12 X0 (M.op (σ y) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq173 X0
       have r₂ := eq12 X0 (M.op (σ y) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq173 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq185 : ∀ X0 : G, (M.op (σ x) X0) ≠ (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) = (k X0 (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq144 eq184
    | (have j0 := eq184 X0
       grind)
    | (have r₁ := eq184 (M.op (σ y) (M.op (σ x) (σ y)))
       have r₂ := eq144 (M.op (σ y) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq184 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq186 : ∀ X0 : G, (M.op (σ x) X0) ≠ (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) X0) = (k X0 (M.op (σ y) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq144 eq185
    | (have j0 := eq185 X0
       grind)
    | exact resolve eq185 eq144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq191 : ∀ X0 X1 : G, (M.op x (M.op (M.op x y) X0)) = (M.op (M.op y X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq86 eq9
    | exact resolve eq9 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ y) X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | exact superpose eq151 eq9
    | exact resolve eq9 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | exact superpose eq156 eq9
    | exact resolve eq9 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq10
    | exact resolve eq10 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq299 : (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) = (σ (M.op y (M.op (M.op x y) x))) := by
    first
    | exact superpose eq201 eq138
    | exact resolve eq138 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq138 X0
       grind)
    | exact superpose eq138 eq10
    | exact resolve eq10 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq327 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op X1 (τ X0)) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq49 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq49
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq341 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66
       have i₂ := eq14 sF2 sF3
       grind)
    | exact superpose eq14 eq66
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq66 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq341
    | exact resolve eq341 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq346 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq342
    | exact resolve eq342 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342
  have eq365 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op y (M.op X0 (M.op (M.op x y) x))) X1) := by
    intro X0 X1
    first
    | exact superpose eq201 eq56
    | exact resolve eq56 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq370 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 X1 (M.op X0 X1)
       have i₂ := eq56 (M.op (M.op X0 X1) (M.op X1 X2)) X1 X0
       grind)
    | exact superpose eq56 eq9
    | exact resolve eq9 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X1))) ≠ (M.op (M.op X1 (M.op X0 X1)) X2) ∨ (M.op X2 (M.op X1 (M.op X0 X1))) = X2 ∨ (M.op (M.op X1 (M.op X0 X1)) X2) = (k X2 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X1 (M.op X0 X1))
       have i₂ := eq56 (M.op X1 (M.op X0 X1)) X1 X0
       grind)
    | exact superpose eq56 eq13
    | (have j0 := eq13 X2 (M.op X1 (M.op X0 X1))
       grind)
    | exact resolve eq13 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X1))) ≠ (M.op (M.op X1 (M.op X0 X1)) X2) ∨ (M.op (M.op X1 (M.op X0 X1)) X2) = (k X2 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq372 X0 X1 X2
       have j1 := eq12 X2 (M.op X1 (M.op X0 X1))
       grind)
    | (have r₁ := eq372 X0 X1 X0
       have r₂ := eq12 X0 (M.op X1 (M.op X0 X1))
       grind)
    | exact resolve eq372 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq395 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X0 (M.op X1 (M.op X0 X1))) ∨ (M.op (M.op X1 (M.op X0 X1)) X2) = (k X2 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq381 X0 X1 X2
       have i₂ := eq56 X2 X1 X0
       grind)
    | exact superpose eq56 eq381
    | (have j0 := eq381 X0 X1 X2
       grind)
    | (have r₁ := eq381 X2 X1 (M.op X1 (M.op X2 X1))
       have r₂ := eq56 (M.op X1 (M.op X2 X1)) X1 X2
       grind)
    | exact resolve eq381 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq396 : ∀ X0 X1 X2 : G, (M.op X0 X2) ≠ (M.op X0 (M.op X1 (M.op X0 X1))) ∨ (M.op X0 X2) = (k X2 (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq395 X0 X1 X2
       have i₂ := eq56 X2 X1 X0
       grind)
    | exact superpose eq56 eq395
    | (have j0 := eq395 X0 X1 X2
       grind)
    | exact resolve eq395 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq398 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq256 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq256
    | exact resolve eq256 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq431 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq302 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq302
    | exact resolve eq302 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302
  have eq525 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X3 X0)) = (M.op X1 (M.op (M.op X1 X2) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq370 X1 X2 (M.op (M.op X2 X3) (M.op X3 X0))
       have i₂ := eq370 X2 X3 X0
       grind)
    | exact superpose eq370 eq370
    | exact resolve eq370 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq526 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X2 X0)) = (M.op X1 (M.op (M.op X1 (M.op X2 X3)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq370 X1 (M.op X2 X3) (M.op X3 (M.op X2 X0))
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq370
    | exact resolve eq370 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 X1 : G, (M.op y (M.op x X0)) = (M.op X1 (M.op (M.op X1 (M.op x y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq52 eq370
    | exact resolve eq370 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq539 : ∀ X0 X1 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (M.op X1 (σ y)) X0)) := by
    intro X0 X1
    first
    | exact superpose eq151 eq370
    | exact resolve eq370 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op (M.op X0 X1) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq370 X1 (M.op X0 X1) X2
       have i₂ := eq56 (M.op (M.op X0 X1) X2) X1 X0
       grind)
    | exact superpose eq56 eq370
    | exact resolve eq370 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X0 X1 X2 : G, (M.op X0 X2) = (M.op (M.op (M.op X1 X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 (M.op X1 X0) (M.op (M.op X1 X0) X1)
       have i₂ := eq370 (M.op X1 X0) X1 X0
       grind)
    | exact superpose eq370 eq56
    | exact resolve eq56 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq643 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X2 X0)) (M.op X1 (M.op X0 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq546 X1 (M.op (M.op X1 X2) (M.op X2 X0)) X3
       have i₂ := eq370 X1 X2 X0
       grind)
    | exact superpose eq370 eq546
    | exact resolve eq546 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq737 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X2 X0)) X3) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq553 (M.op (M.op X1 X2) (M.op X2 X0)) X1 X3
       have i₂ := eq370 X1 X2 X0
       grind)
    | exact superpose eq370 eq553
    | exact resolve eq553 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq738 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X1 X2) X0)) X3) = (M.op (M.op X0 X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq553 (M.op X1 (M.op (M.op X1 X2) X0)) X2 X3
       have i₂ := eq546 X1 X2 X0
       grind)
    | exact superpose eq546 eq553
    | exact resolve eq553 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq739 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X2 X0)) X3) = (M.op (M.op X0 (M.op X2 X1)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq553 (M.op X1 (M.op X2 X0)) (M.op X2 X1) X3
       have i₂ := eq9 X0 X2 X1
       grind)
    | exact superpose eq9 eq553
    | exact resolve eq553 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq740 : ∀ X0 : G, (M.op (M.op x (M.op x y)) X0) = (M.op (M.op y (M.op x (M.op y (M.op x y)))) X0) := by
    intro X0
    first
    | exact superpose eq163 eq553
    | exact resolve eq553 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 : G, (M.op (M.op x (M.op (σ x) (σ y))) X0) = (M.op (M.op (σ y) (M.op (σ x) (M.op y (M.op x y)))) X0) := by
    intro X0
    first
    | exact superpose eq164 eq553
    | exact resolve eq553 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq751 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op y X0)) X1) = (M.op (M.op X0 x) X1) := by
    intro X0 X1
    first
    | exact superpose eq156 eq553
    | exact resolve eq553 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq752 : ∀ X0 X1 : G, (M.op (M.op x (M.op (M.op x y) X0)) X1) = (M.op (M.op X0 y) X1) := by
    intro X0 X1
    first
    | exact superpose eq86 eq553
    | exact resolve eq553 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq753 : ∀ X0 X1 : G, (M.op (M.op y (M.op x X0)) X1) = (M.op (M.op X0 (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq52 eq553
    | exact resolve eq553 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq756 : ∀ X0 X1 : G, (M.op (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) X1) = (M.op (M.op X0 (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq151 eq553
    | exact resolve eq553 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq757 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (σ x) X0)) X1) = (M.op (M.op X0 (M.op (σ x) (σ y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq58 eq553
    | exact resolve eq553 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : (σ y) = (M.op (M.op (M.op x y) (M.op y (σ x))) (M.op x (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq164
       have i₂ := eq739 sF0 sF2 y (M.op x sF4)
       grind)
    | (have i₁ := eq164
       have i₂ := eq739 sF2 sF0 y (M.op x sF4)
       grind)
    | exact superpose eq739 eq164
    | exact resolve eq164 eq739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq739
  have eq936 : ∀ X0 X1 : G, (M.op (M.op y (M.op x y)) (M.op (M.op X0 y) (M.op (M.op (M.op x y) X0) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq79 eq53
    | exact resolve eq53 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq988 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 X0)) = (M.op X1 (M.op (M.op X2 (M.op X3 X1)) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X1 X3 X2 (M.op X2 (M.op X3 X0))
       have i₂ := eq9 X0 X3 X2
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1014 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X2) (M.op X2 X0)) = (M.op (M.op X3 (M.op X4 X1)) (M.op (M.op X4 X3) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op (M.op X3 (M.op X4 X1)) (M.op (M.op X4 X3) X0)) X1 X2
       have i₂ := eq53 X1 X4 X3 X0
       grind)
    | exact superpose eq53 eq9
    | exact resolve eq9 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1027 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X3 (M.op X4 (M.op X2 X1))) (M.op (M.op X4 X3) X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq546 X2 X1 (M.op (M.op X3 (M.op X4 (M.op X2 X1))) (M.op (M.op X4 X3) X0))
       have i₂ := eq53 (M.op X2 X1) X4 X3 X0
       grind)
    | exact superpose eq53 eq546
    | exact resolve eq546 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq1033 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op X1 (M.op X2 (σ x))) (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 (M.op (M.op X2 (M.op X1 sF2)) (M.op (M.op X1 X2) x))
       have i₂ := eq53 sF2 X1 X2 x
       grind)
    | exact superpose eq53 eq58
    | exact resolve eq58 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1123 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 y) (M.op (M.op (M.op x y) X0) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq80 eq936
    | exact resolve eq936 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq1157 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) (M.op X2 X0)) (M.op X1 X3)) = (M.op (M.op X0 X4) (M.op X4 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X3 X1 (M.op (M.op X1 X2) (M.op X2 X0)) X4
       have i₂ := eq370 X1 X2 X0
       grind)
    | exact superpose eq370 eq55
    | exact resolve eq55 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1161 : ∀ X0 X1 : G, (M.op (M.op y X1) (M.op X1 X0)) = (M.op (M.op x (M.op x y)) (M.op (M.op x (M.op y (M.op x y))) X0)) := by
    intro X0 X1
    first
    | exact superpose eq163 eq55
    | exact resolve eq55 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1162 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) (M.op X1 X0)) = (M.op (M.op x (M.op (σ x) (σ y))) (M.op (M.op (M.op x y) (M.op y (σ x))) X0)) := by
    intro X0 X1
    first
    | exact superpose eq814 eq55
    | exact resolve eq55 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq1173 : ∀ X0 X1 X2 : G, (M.op (M.op y (M.op x X0)) (M.op (M.op x y) X1)) = (M.op (M.op X0 X2) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1179 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (σ x) X0)) (M.op (M.op (σ x) (σ y)) X1)) = (M.op (M.op X0 X2) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | exact superpose eq58 eq55
    | exact resolve eq55 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1182 : ∀ X0 : G, (M.op y (M.op (M.op x (M.op x y)) X0)) = (M.op (M.op y (M.op x y)) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq163 eq55
    | exact resolve eq55 eq163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq1193 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op (M.op X3 X4) (M.op X4 X0)))) = (M.op (M.op (M.op X2 X1) X3) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op (M.op X3 X4) (M.op X4 X0)) X2 X1 X3
       have i₂ := eq370 X3 X4 X0
       grind)
    | exact superpose eq370 eq55
    | exact resolve eq55 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1195 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 (M.op X3 (M.op X4 X0)))) = (M.op (M.op (M.op X2 X1) (M.op X4 X3)) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 (M.op X3 (M.op X4 X0)) X2 X1 (M.op X4 X3)
       have i₂ := eq9 X0 X4 X3
       grind)
    | exact superpose eq9 eq55
    | exact resolve eq55 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1207 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y X0)))) = (M.op (M.op (M.op X2 X1) x) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq156 eq55
    | exact resolve eq55 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1208 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x (M.op (M.op x y) X0)))) = (M.op (M.op (M.op X2 X1) y) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq86 eq55
    | exact resolve eq55 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1209 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op y (M.op x X0)))) = (M.op (M.op (M.op X2 X1) (M.op x y)) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq55
    | exact resolve eq55 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1215 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (σ y) (M.op (σ x) X0)))) = (M.op (M.op (M.op X2 X1) (M.op (σ x) (σ y))) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq58 eq55
    | exact resolve eq55 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq1227 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op X1 X0) (M.op X1 X0))) (τ (M.op (M.op X1 X0) (M.op X1 X0)))) = (τ (M.op X0 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq431 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq55 (M.op X1 X0) X1 X0 (M.op X1 X0)
       grind)
    | exact superpose eq55 eq431
    | exact resolve eq431 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1243 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X1 (M.op X1 X0)))) = (M.op (M.op (τ (M.op X1 X0)) (τ (M.op X1 X0))) (M.op (τ (M.op X1 X0)) (τ (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1227 X0 X1
       have i₂ := eq431 (M.op X1 X0)
       grind)
    | exact superpose eq431 eq1227
    | exact resolve eq1227 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431 eq1227
  have eq1247 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (σ y) (M.op (σ x) X0)))) = (M.op (M.op (σ y) (M.op (σ x) (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq757 eq1215
    | exact resolve eq1215 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq1253 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op y (M.op x X0)))) = (M.op (M.op y (M.op x (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq753 eq1209
    | exact resolve eq1209 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1254 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x (M.op (M.op x y) X0)))) = (M.op (M.op x (M.op (M.op x y) (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1208 X0 X1 X2
       have i₂ := eq752 (M.op X2 X1) X0
       grind)
    | exact superpose eq752 eq1208
    | exact resolve eq1208 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1255 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y X0)))) = (M.op (M.op (M.op x y) (M.op y (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1207 X0 X1 X2
       have i₂ := eq751 (M.op X2 X1) X0
       grind)
    | exact superpose eq751 eq1207
    | exact resolve eq1207 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751 eq1207
  have eq1263 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 (M.op X2 (M.op X1 (M.op X0 X3)))))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq643 X0 X1 X2 X3
       have i₂ := eq1195 (M.op X1 (M.op X0 X3)) X2 X1 X0 X2
       grind)
    | exact superpose eq1195 eq643
    | exact resolve eq643 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq1265 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X3) = (M.op X2 (M.op X1 (M.op X0 (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq737 X0 X1 X2 X3
       have i₂ := eq1195 X3 X2 X1 X0 X2
       grind)
    | exact superpose eq1195 eq737
    | exact resolve eq737 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq1284 : ∀ X0 : G, (M.op y (M.op (M.op x (M.op x y)) X0)) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq80 eq1182
    | exact resolve eq1182 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq1182
  have eq1290 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op y (M.op x (σ y))) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq197 x x
       have i₂ := eq1173 sF3 x x
       grind)
    | exact superpose eq1173 eq197
    | exact resolve eq197 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq1299 : ∀ X0 : G, (M.op (M.op x (M.op (σ x) (σ y))) (M.op (M.op (M.op x y) (M.op y (σ x))) X0)) = (M.op (M.op y (M.op x (σ y))) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq1162 x x
       have i₂ := eq1173 sF3 x x
       grind)
    | exact superpose eq1173 eq1162
    | exact resolve eq1162 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162 eq1173
  have eq1300 : ∀ X0 : G, (M.op x (M.op (M.op x y) X0)) = (M.op (M.op x (M.op x y)) (M.op (M.op x (M.op y (M.op x y))) X0)) := by
    intro X0
    first
    | (have i₁ := eq1161 X0 x
       have i₂ := eq191 X0 x
       grind)
    | exact superpose eq191 eq1161
    | exact resolve eq1161 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq1161
  have eq1302 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X4) (M.op X4 X3)) = (M.op X2 (M.op X1 (M.op X0 (M.op X2 (M.op X1 X3))))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1157 X0 X1 X2 X3 X4
       have i₂ := eq1195 (M.op X1 X3) X2 X1 X0 X2
       grind)
    | exact superpose eq1195 eq1157
    | exact resolve eq1157 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq1305 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X1 (M.op X1 X0)))) = (M.op (M.op (σ y) (M.op (σ x) (τ (M.op X1 X0)))) (M.op (M.op (σ x) (σ y)) (τ (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1243 X0 X1
       have i₂ := eq1179 (τ (M.op X1 X0)) (τ (M.op X1 X0)) (τ (M.op X1 X0))
       grind)
    | exact superpose eq1179 eq1243
    | exact resolve eq1243 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243
  have eq1307 : ∀ X0 : G, (M.op (M.op x (M.op (σ x) (σ y))) X0) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (σ x) X0)))) := by
    intro X0
    first
    | exact superpose eq1247 eq742
    | exact resolve eq742 eq1247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq1247
  have eq1312 : ∀ X0 : G, (M.op (M.op x (M.op x y)) X0) = (M.op (M.op x y) (M.op y (M.op y (M.op x X0)))) := by
    intro X0
    first
    | (have i₁ := eq740 X0
       have i₂ := eq1253 X0 sF0 y
       grind)
    | exact superpose eq1253 eq740
    | exact resolve eq740 eq1253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740 eq1253
  have eq1338 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op x (M.op (σ x) (σ y))) (M.op (M.op (M.op x y) (M.op y (σ x))) X0)) := by
    intro X0
    first
    | exact superpose eq1290 eq1299
    | exact resolve eq1299 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290 eq1299
  have eq1362 : ∀ X0 : G, (M.op x (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op y (M.op y (M.op x (M.op (M.op x (M.op y (M.op x y))) X0))))) := by
    intro X0
    first
    | exact superpose eq1312 eq1300
    | exact resolve eq1300 eq1312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300
  have eq1363 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op x X0))))) := by
    intro X0
    first
    | exact superpose eq1312 eq1284
    | exact resolve eq1284 eq1312
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1284 eq1312
  have eq1377 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (σ x) (M.op (M.op (M.op x y) (M.op y (σ x))) X0))))) := by
    intro X0
    first
    | exact superpose eq1307 eq1338
    | exact resolve eq1338 eq1307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307 eq1338
  have eq1386 : ∀ X0 : G, (M.op x (M.op (M.op x y) X0)) = (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) (M.op y X0))))) := by
    intro X0
    first
    | (have i₁ := eq1362 X0
       have i₂ := eq526 X0 x y sF0
       grind)
    | exact superpose eq526 eq1362
    | exact resolve eq1362 eq526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526 eq1362
  have eq1390 : ∀ X0 : G, (M.op (σ x) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))) := by
    intro X0
    first
    | (have i₁ := eq1377 X0
       have i₂ := eq988 X0 sF2 sF0 y
       grind)
    | exact superpose eq988 eq1377
    | exact resolve eq1377 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988 eq1377
  have eq1395 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 (σ y)) X0)) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))) := by
    intro X0 X1
    first
    | exact superpose eq1390 eq539
    | exact resolve eq539 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq1397 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))) X1) := by
    intro X0 X1
    first
    | exact superpose eq1390 eq756
    | exact resolve eq756 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq1421 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) X1) = (M.op (M.op (M.op x y) (M.op y X0)) (M.op (σ y) (M.op (M.op x y) (M.op y X1)))) := by
    intro X0 X1
    first
    | exact superpose eq1255 eq1397
    | exact resolve eq1397 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397
  have eq1547 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op y (M.op (M.op X1 (M.op x y)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X1 (M.op X1 (M.op x X0))
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq92
    | exact resolve eq92 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1564 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op x y)) (M.op (M.op x X1) X0)) X2) = (M.op (M.op X0 y) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq92 eq553
    | exact resolve eq553 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq1565 : ∀ X0 X1 X2 : G, (M.op (M.op X0 y) X2) = (M.op (M.op x y) (M.op X1 (M.op X0 (M.op (M.op x X1) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1564 x X2 X0
       have i₂ := eq1195 X0 sF0 X2 x (M.op x X2)
       grind)
    | exact superpose eq1195 eq1564
    | exact resolve eq1564 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1564
  have eq1621 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) X0)) = (M.op (σ y) (M.op (M.op X1 (M.op (σ x) (σ y))) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq98 x (M.op x (M.op sF2 X0))
       have i₂ := eq9 X0 sF2 x
       grind)
    | exact superpose eq9 eq98
    | exact resolve eq98 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1628 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) X0) = (M.op (M.op (M.op X1 (M.op (σ x) (σ y))) (σ y)) X0) := by
    intro X0 X1
    first
    | exact superpose eq98 eq9
    | exact resolve eq9 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1637 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op (M.op (σ x) X1) X0)) X2) = (M.op (M.op X0 (σ y)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq98 eq553
    | exact resolve eq553 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq1638 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ y)) X2) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 (M.op (M.op (σ x) X1) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1637 x X2 X0
       have i₂ := eq1195 X0 sF4 X2 x (M.op sF2 X2)
       grind)
    | exact superpose eq1195 eq1637
    | exact resolve eq1637 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq1637
  have eq1647 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) X0) = (M.op (M.op (M.op x y) (M.op y (M.op X1 (M.op (σ x) (σ y))))) (M.op (σ y) (M.op (M.op x y) (M.op y X0)))) := by
    intro X0 X1
    first
    | exact superpose eq1421 eq1628
    | exact resolve eq1628 eq1421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628
  have eq1669 : ∀ X0 X1 : G, (M.op (M.op (σ x) X1) X0) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))) := by
    intro X0 X1
    first
    | exact superpose eq1255 eq1647
    | exact resolve eq1647 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647
  have eq1684 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ y)) X2) = (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X2)))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1669 eq1638
    | exact resolve eq1638 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1638
  have eq2234 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (M.op X1 X0)) X2) = (M.op (M.op X0 (M.op X1 (M.op (σ y) (M.op (σ x) (σ y))))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq178 eq553
    | exact resolve eq553 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq2235 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (M.op (σ y) (M.op (σ x) (σ y))))) X2) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 X0) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X2))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1669 eq2234
    | exact resolve eq2234 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669 eq2234
  have eq2363 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op (σ x) (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq535 eq144
    | exact resolve eq144 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq535
  have eq2378 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op (σ x) (M.op (M.op y (M.op x (M.op (σ y) (M.op (σ x) (σ y))))) X0)) := by
    intro X0
    first
    | exact superpose eq753 eq2363
    | exact resolve eq2363 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753 eq2363
  have eq2409 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0)))))))) := by
    intro X0
    first
    | exact superpose eq2235 eq2378
    | exact resolve eq2378 eq2235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2235 eq2378
  have eq2426 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))) := by
    intro X0
    first
    | exact superpose eq1390 eq2409
    | exact resolve eq2409 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2409
  have eq2431 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))) := by
    intro X0
    first
    | (have i₁ := eq2426 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2426
    | (have j0 := eq2426 X0
       grind)
    | exact resolve eq2426 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2426
  have eq2659 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op x (M.op (M.op X1 y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1123 x (M.op x (M.op sF0 X0))
       have i₂ := eq9 X0 sF0 x
       grind)
    | exact superpose eq9 eq1123
    | exact resolve eq1123 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq2775 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op (M.op (M.op x y) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1547 x (M.op sF0 X0)
       have i₂ := eq553 X0 sF0 x
       grind)
    | exact superpose eq553 eq1547
    | exact resolve eq1547 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2776 : ∀ X0 X1 : G, (M.op y X0) = (M.op X1 (M.op x (M.op (M.op x y) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1547 (M.op sF0 (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1 sF0
       grind)
    | exact superpose eq9 eq1547
    | exact resolve eq1547 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2797 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op x y)) X1) X2) = (M.op (M.op (M.op X0 (M.op x X1)) y) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq1547 eq553
    | exact resolve eq553 eq1547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553 eq1547
  have eq2798 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op x y)) X1) X2) = (M.op (M.op x (M.op (M.op x y) (M.op X0 (M.op x X1)))) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2797 X0 X1 X2
       have i₂ := eq752 (M.op X0 (M.op x X1)) X2
       grind)
    | exact superpose eq752 eq2797
    | exact resolve eq2797 eq752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2797
  have eq2823 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (M.op x y)) X1) X2) = (M.op (M.op x X1) (M.op X0 (M.op x (M.op (M.op x y) X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1254 eq2798
    | exact resolve eq2798 eq1254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2798
  have eq2852 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op X1 (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1621 (M.op sF4 (M.op X1 X0)) X1
       have i₂ := eq9 X0 X1 sF4
       grind)
    | exact superpose eq9 eq1621
    | exact resolve eq1621 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2869 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op X2 (M.op (M.op X2 (σ y)) (M.op X0 (M.op (σ x) X1)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1621 eq370
    | exact resolve eq370 eq1621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370 eq1621
  have eq2875 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) X1) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (σ x) X1))))))) := by
    intro X0 X1
    first
    | exact superpose eq1395 eq2869
    | exact resolve eq2869 eq1395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395 eq2869
  have eq2888 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 X0))))))) := by
    intro X0 X1
    first
    | exact superpose eq1390 eq2852
    | exact resolve eq2852 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2852
  have eq2900 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (σ x) X0)) X1) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (σ x) X1))))))) := by
    intro X0 X1
    first
    | exact superpose eq2875 eq757
    | exact resolve eq757 eq2875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757 eq2875
  have eq2942 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X2 X1)) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (σ x) (M.op (M.op (σ x) (σ y)) X1)))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2900 eq1179
    | exact resolve eq1179 eq2900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179
  have eq2947 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X1 (M.op X1 X0)))) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (τ (M.op X1 X0)) (M.op (σ x) (M.op (M.op (σ x) (σ y)) (τ (M.op X1 X0)))))))))) := by
    intro X0 X1
    first
    | exact superpose eq2900 eq1305
    | exact resolve eq1305 eq2900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305 eq2900
  have eq2963 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X1 (M.op X1 X0)))) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (τ (M.op X1 X0)) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (τ (M.op X1 X0))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq1390 eq2947
    | exact resolve eq2947 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2947
  have eq2965 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X2 X1)) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X1))))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1390 eq2942
    | exact resolve eq2942 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390 eq2942
  have eq2980 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X1 X2) X0)) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq525 X0 X1 X2 x
       have i₂ := eq2965 X2 X0 x
       grind)
    | exact superpose eq2965 eq525
    | exact resolve eq525 eq2965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq2982 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X3 (M.op X4 X1)) (M.op (M.op X4 X3) X0)) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq1014 X0 X1 x X3 X4
       have i₂ := eq2965 X1 X0 x
       grind)
    | exact superpose eq2965 eq1014
    | exact resolve eq1014 eq2965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1014
  have eq2986 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X1) X3) X0) = (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1193 X0 X1 X2 X3 x
       have i₂ := eq2965 X3 X0 x
       grind)
    | exact superpose eq2965 eq1193
    | exact resolve eq1193 eq2965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193
  have eq2989 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 (M.op X2 (M.op X1 X3))))) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1302 X0 X1 X2 X3 x
       have i₂ := eq2965 X0 X3 x
       grind)
    | exact superpose eq2965 eq1302
    | exact resolve eq1302 eq2965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1302 eq2965
  have eq3012 : ∀ X0 X2 : G, (M.op (M.op X0 (σ y)) X2) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X2)))))))))))))))) := by
    intro X0 X2
    first
    | (have i₁ := eq1684 X0 x X2
       have i₂ := eq2989 X0 x sF4 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y X2)))))
       grind)
    | exact superpose eq2989 eq1684
    | exact resolve eq1684 eq2989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684 eq2989
  have eq3016 : ∀ X0 X1 X2 : G, (M.op (M.op x X1) (M.op X0 (M.op x (M.op (M.op x y) X2)))) = (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X2))))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2823 X2 x X0
       have i₂ := eq2986 X0 sF0 X2 x
       grind)
    | exact superpose eq2986 eq2823
    | exact resolve eq2823 eq2986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2823
  have eq3035 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op X2 X1) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1027 X0 X1 X2 x x
       have i₂ := eq2982 X0 (M.op X2 X1) x x
       grind)
    | exact superpose eq2982 eq1027
    | exact resolve eq1027 eq2982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1027
  have eq3039 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (σ x) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))) := by
    intro X0
    first
    | (have i₁ := eq1033 X0 x x
       have i₂ := eq2982 X0 sF2 x x
       grind)
    | exact superpose eq2982 eq1033
    | exact resolve eq1033 eq2982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1033
  have eq3048 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))) X3) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq738 X0 x X2 X3
       have i₂ := eq2980 X0 x X2
       grind)
    | exact superpose eq2980 eq738
    | exact resolve eq738 eq2980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738 eq2980
  have eq3077 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op y X0)) (M.op (σ y) (M.op (M.op x y) (M.op y X1)))) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X1)))))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq3012 eq1421
    | exact resolve eq1421 eq3012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421 eq3012
  have eq3107 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0)))))))) (M.op (σ y) (M.op (M.op x y) (M.op y X3)))) := by
    intro X0 X2 X3
    first
    | exact superpose eq1255 eq3048
    | exact resolve eq3048 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3048
  have eq3151 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0)))))) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3)))))))))))))))) := by
    intro X0 X2 X3
    first
    | exact superpose eq3077 eq3107
    | exact resolve eq3107 eq3077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3107
  have eq3174 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))) (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3))))))) := by
    intro X0 X2 X3
    first
    | exact superpose eq3035 eq3151
    | exact resolve eq3151 eq3035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3151
  have eq3189 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op (M.op x y) (M.op y X0)) (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3)))))))))) := by
    intro X0 X2 X3
    first
    | exact superpose eq1255 eq3174
    | exact resolve eq3174 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255 eq3174
  have eq3203 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3)))))))))))))))))))))) := by
    intro X0 X2 X3
    first
    | exact superpose eq3077 eq3189
    | exact resolve eq3189 eq3077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3077 eq3189
  have eq3227 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op x (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2659 X0 X1
       have i₂ := eq3203 X1 y X0
       grind)
    | exact superpose eq3203 eq2659
    | exact resolve eq2659 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2659
  have eq3228 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X1 (M.op X0 (M.op (M.op x X1) X2)))) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X2)))))))))))))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1565 X0 X1 X2
       have i₂ := eq3203 X0 y X2
       grind)
    | exact superpose eq3203 eq1565
    | exact resolve eq1565 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565
  have eq3229 : ∀ X0 X1 : G, (M.op (M.op x (M.op (M.op x y) X0)) X1) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X1)))))))))))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq752 X0 X1
       have i₂ := eq3203 X0 y X1
       grind)
    | exact superpose eq3203 eq752
    | exact resolve eq752 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752
  have eq3234 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op X2 X1) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0)))))))))))))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X0 X1 X2
       have i₂ := eq3203 X1 (M.op X2 X1) X0
       grind)
    | exact superpose eq3203 eq56
    | exact resolve eq56 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq3242 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 (M.op X2 X3)))) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3)))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1265 X0 X1 X2 X3
       have i₂ := eq3203 X0 X1 X3
       grind)
    | exact superpose eq3203 eq1265
    | exact resolve eq1265 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265
  have eq3246 : ∀ X0 X1 X3 X4 : G, (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))) = (M.op (M.op X3 (M.op X4 X1)) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X4 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))))))))))))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq2982 X0 X1 X3 X4
       have i₂ := eq3203 X4 X3 X0
       grind)
    | exact superpose eq3203 eq2982
    | exact resolve eq2982 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2982
  have eq3247 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3)))))))))))))))))))))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2986 X0 X1 X2 X3
       have i₂ := eq3203 X2 X1 X3
       grind)
    | exact superpose eq3203 eq2986
    | exact resolve eq2986 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2986
  have eq3269 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0)))))))))))))))))))))))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3035 X0 X2 X0
       have i₂ := eq3203 X0 X2 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y X0)))))
       grind)
    | exact superpose eq3203 eq3035
    | exact resolve eq3035 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3035
  have eq3280 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X2))))))))))))) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op x (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op x (M.op (M.op x y) X2))))))))))))))))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3016 X0 X2 X2
       have i₂ := eq3203 x X2 (M.op X0 (M.op x (M.op sF0 X2)))
       grind)
    | exact superpose eq3203 eq3016
    | exact resolve eq3016 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3016
  have eq3290 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x (M.op (M.op x y) X0)))) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op x (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op (M.op x y) (M.op X2 X1)) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0)))))))))))))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1254 x X1 X2
       have i₂ := eq3203 x (M.op sF0 (M.op X2 X1)) x
       grind)
    | exact superpose eq3203 eq1254
    | exact resolve eq1254 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254
  have eq3301 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op X0 (M.op (M.op x y) x)) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X1)))))))))))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq365 X0 x
       have i₂ := eq3203 y (M.op X0 (M.op sF0 x)) x
       grind)
    | exact superpose eq3203 eq365
    | exact resolve eq365 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365
  have eq3310 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op x X1))))))))))))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2775 x X1
       have i₂ := eq3203 sF0 x (M.op x X1)
       grind)
    | exact superpose eq3203 eq2775
    | exact resolve eq2775 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2775
  have eq3358 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y (M.op x (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op x X1)))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq2431 eq3310
    | exact resolve eq3310 eq2431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3310
  have eq3367 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op x (M.op (M.op x y) (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op X0 (M.op (M.op x y) x)) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X1))))))))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq1386 eq3301
    | exact resolve eq3301 eq1386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3301
  have eq3377 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x (M.op (M.op x y) X0)))) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op (M.op x y) (M.op X2 X1)) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq3290
    | exact resolve eq3290 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3290
  have eq3387 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X2))))))))))))) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op x (M.op (M.op x y) X2)))))))))))))))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq3280
    | exact resolve eq3280 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3280
  have eq3416 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3))))))))))))))))))))) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0)))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3247 X3 X1 X2 X3
       have i₂ := eq3203 sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y (M.op X2 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y (M.op X1 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y X3))))))))))))))))))))) X3
       grind)
    | exact superpose eq3203 eq3247
    | exact resolve eq3247 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3247
  have eq3417 : ∀ X0 X1 X3 X4 : G, (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op X4 X1) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X4 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0)))))))))))))))))))))))))))))))))))))))))))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq3246 X0 X1 X0 X4
       have i₂ := eq3203 X0 (M.op X4 X1) (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y (M.op X4 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y (M.op X0 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y X0))))))))))))))))))))))
       grind)
    | exact superpose eq3203 eq3246
    | exact resolve eq3246 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3246
  have eq3428 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))))))))))))))))))))))))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3234 X0 X2 X0
       have i₂ := eq3203 X0 X2 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y X0)))))
       grind)
    | exact superpose eq3203 eq3234
    | exact resolve eq3234 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3234
  have eq3431 : ∀ X0 X1 : G, (M.op (M.op x (M.op (M.op x y) X0)) X1) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X1)))))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq2888 eq3229
    | exact resolve eq3229 eq2888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3229
  have eq3432 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X1 (M.op X0 (M.op (M.op x X1) X2)))) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X2)))))))))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2888 eq3228
    | exact resolve eq3228 eq2888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3228
  have eq3433 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0)))))))))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq156 eq3227
    | exact resolve eq3227 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3227
  have eq3467 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op x X1))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq86 eq3358
    | exact resolve eq3358 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3358
  have eq3476 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op X0 (M.op (M.op x y) x)) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X1)))))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq2776 eq3367
    | exact resolve eq3367 eq2776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3367
  have eq3486 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x (M.op (M.op x y) X0)))) = (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op (M.op x y) (M.op X2 X1)) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3377 X0 X1 X2
       have i₂ := eq1263 sF3 y sF0 (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y (M.op (M.op sF0 (M.op X2 X1)) (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y X0)))))))))))))
       grind)
    | exact superpose eq1263 eq3377
    | exact resolve eq3377 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3377
  have eq3496 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X2))))))))))))) = (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op x (M.op (M.op x y) X2)))))))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3387 X0 X1 X2
       have i₂ := eq1263 sF3 y sF0 (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y (M.op X1 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y (M.op X0 (M.op x (M.op sF0 X2))))))))))))))))
       grind)
    | exact superpose eq1263 eq3387
    | exact resolve eq3387 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3387
  have eq3514 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op x (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3))))))))))))))))))))) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq2431 eq3416
    | exact resolve eq3416 eq2431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3416
  have eq3515 : ∀ X0 X1 X3 X4 : G, (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op X4 (M.op (M.op X4 X1) (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0)))))))))))))) := by
    intro X0 X1 X3 X4
    first
    | exact superpose eq3269 eq3417
    | exact resolve eq3417 eq3269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3269 eq3417
  have eq3526 : ∀ X0 X1 : G, (M.op (M.op x (M.op (M.op x y) X0)) X1) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) X1)))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3431 X0 x
       have i₂ := eq1263 y sF0 sF3 x
       grind)
    | exact superpose eq1263 eq3431
    | exact resolve eq3431 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3431
  have eq3527 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X1 (M.op X0 (M.op (M.op x X1) X2)))) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) X2)))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3432 X0 X1 x
       have i₂ := eq1263 y sF0 sF3 x
       grind)
    | exact superpose eq1263 eq3432
    | exact resolve eq3432 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3432
  have eq3528 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0)))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq2888 eq3433
    | exact resolve eq3433 eq2888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3433
  have eq3555 : ∀ X0 X1 : G, (M.op y (M.op X0 X1)) = (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) X1)))))))) := by
    intro X0 X1
    first
    | exact superpose eq52 eq3467
    | exact resolve eq3467 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3467
  have eq3564 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op X0 (M.op (M.op x y) x)) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X1))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq1386 eq3476
    | exact resolve eq3476 eq1386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3476
  have eq3574 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x (M.op (M.op x y) X0)))) = (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op X2 X1) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0)))))))))))))))))))))))))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3486 X0 X1 X2
       have i₂ := eq3203 sF0 (M.op X2 X1) (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y X0)))))
       grind)
    | exact superpose eq3203 eq3486
    | exact resolve eq3486 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3486
  have eq3589 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3))))))))))))))))))))) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0)))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq86 eq3514
    | exact resolve eq3514 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3514
  have eq3590 : ∀ X0 X1 X3 X4 : G, (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op X4 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X4 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))))))))))))))))))))))))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq3515 X0 x X3 X0
       have i₂ := eq3203 X0 x (M.op X3 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y X0))))))
       grind)
    | exact superpose eq3203 eq3515
    | exact resolve eq3515 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3515
  have eq3599 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) X1)))))))))) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op x (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op (M.op x y) X0) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X1)))))))))))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3526 X0 x
       have i₂ := eq3203 x (M.op sF0 X0) x
       grind)
    | exact superpose eq3203 eq3526
    | exact resolve eq3526 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3526
  have eq3600 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) X2)))))))))) = (M.op (M.op x y) (M.op X1 (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op x (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X2))))))))))))))))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3527 X0 X1 X2
       have i₂ := eq3203 x X1 X2
       grind)
    | exact superpose eq3203 eq3527
    | exact resolve eq3527 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3527
  have eq3601 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) X0)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3528 x X1
       have i₂ := eq1263 y sF0 sF3 x
       grind)
    | exact superpose eq1263 eq3528
    | exact resolve eq3528 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3528
  have eq3632 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y X3)))))))))))))))) := by
    intro X0 X2 X3
    first
    | exact superpose eq3555 eq3203
    | exact resolve eq3203 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3203
  have eq3635 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 (M.op X2 X3)))) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y X3)))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq3555 eq3242
    | exact resolve eq3242 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3242
  have eq3647 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op x (M.op (M.op x y) X2)))))))))))))))) = (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y X2))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3555 eq3496
    | exact resolve eq3496 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3496
  have eq3665 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))))))))))))))))))))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3555 eq3428
    | exact resolve eq3428 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3428
  have eq3684 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X1 (M.op X1 X0)))) = (M.op (M.op x y) (M.op y (M.op (τ (M.op X1 X0)) (M.op (M.op x y) (M.op y (τ (M.op X1 X0))))))) := by
    intro X0 X1
    first
    | exact superpose eq3555 eq2963
    | exact resolve eq2963 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2963
  have eq3685 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y X0))))) := by
    intro X0
    first
    | exact superpose eq3555 eq2431
    | exact resolve eq2431 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2431
  have eq3686 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op x y) (M.op y (M.op (σ x) (M.op (M.op x y) (M.op y X0))))) := by
    intro X0
    first
    | exact superpose eq3555 eq3039
    | exact resolve eq3039 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3039
  have eq3696 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op X0 (M.op (M.op x y) x)) (M.op (M.op x y) (M.op y X1))))))) := by
    intro X0 X1
    first
    | exact superpose eq3555 eq3564
    | exact resolve eq3564 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3564
  have eq3706 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x (M.op (M.op x y) X0)))) = (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op X2 X1) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0)))))))))))))))))))))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3555 eq3574
    | exact resolve eq3574 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3574
  have eq3721 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3))))))))))))))))))))) (M.op (M.op x y) (M.op y X0)))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq3555 eq3589
    | exact resolve eq3589 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3589
  have eq3722 : ∀ X0 X1 X3 : G, (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))))))))))))))))))) := by
    intro X0 X1 X3
    first
    | exact superpose eq2888 eq3590
    | exact resolve eq3590 eq2888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3590
  have eq3731 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) X1)))))))))) = (M.op (M.op x y) (M.op y (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op (M.op x y) X0) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X1)))))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq3555 eq3599
    | exact resolve eq3599 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3599
  have eq3732 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) X2)))))))))) = (M.op (M.op x y) (M.op X1 (M.op X0 (M.op (M.op x y) (M.op y (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X2))))))))))))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3555 eq3600
    | exact resolve eq3600 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3600
  have eq3764 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))))))))))))))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3555 eq3665
    | exact resolve eq3665 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3665
  have eq3777 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y X2))))))) = (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op X0 (M.op x (M.op (M.op x y) X2)))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3555 eq3647
    | exact resolve eq3647 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3647
  have eq3789 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 (M.op X2 X3)))) = (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y X3)))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq3555 eq3635
    | exact resolve eq3635 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3635
  have eq3792 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y X3)))))))))) := by
    intro X0 X2 X3
    first
    | exact superpose eq3555 eq3632
    | exact resolve eq3632 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3632
  have eq3811 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x (M.op (M.op x y) X0)))) = (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op y (M.op x (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op X2 X1) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))))))))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3685 eq3706
    | exact resolve eq3706 eq3685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3706
  have eq3824 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3))))))))))))))) (M.op (M.op x y) (M.op y X0)))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq3555 eq3721
    | exact resolve eq3721 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3721
  have eq3825 : ∀ X0 X1 X3 : G, (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))) = (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))))))))))))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq3722 X0 X1 X3
       have i₂ := eq1263 y sF0 sF3 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y (M.op X1 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y (M.op X3 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y X0)))))))))))))))))
       grind)
    | exact superpose eq1263 eq3722
    | exact resolve eq3722 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3722
  have eq3834 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) X1)))))))))) = (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op (M.op x y) X0) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X1))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq52 eq3731
    | exact resolve eq3731 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3731
  have eq3835 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) X2)))))))))) = (M.op (M.op x y) (M.op X1 (M.op X0 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X2)))))))))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq3732
    | exact resolve eq3732 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3732
  have eq3863 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))))))))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3555 eq3764
    | exact resolve eq3764 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3764
  have eq3885 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op (M.op x y) x) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X1)))))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3696 X0 X1
       have i₂ := eq3792 X0 (M.op sF0 x) (M.op sF0 (M.op y X1))
       grind)
    | exact superpose eq3792 eq3696
    | exact resolve eq3696 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3696
  have eq3899 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x (M.op (M.op x y) X0)))) = (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op X2 X1) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0)))))))))))))))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3777 eq3811
    | exact resolve eq3811 eq3777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3777 eq3811
  have eq3911 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op X2 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3)))))))))))))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3824 X0 X1 X2 X3
       have i₂ := eq3792 y (M.op X2 (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y (M.op X1 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y X3)))))))))))))) (M.op sF0 (M.op y X0))
       grind)
    | exact superpose eq3792 eq3824
    | exact resolve eq3824 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3824
  have eq3912 : ∀ X0 X1 X3 : G, (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))) = (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))))))) := by
    intro X0 X1 X3
    first
    | exact superpose eq3555 eq3825
    | exact resolve eq3825 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3825
  have eq3921 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) X1)))))))))) = (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op (M.op x y) X0) (M.op (M.op x y) (M.op y X1))))))) := by
    intro X0 X1
    first
    | exact superpose eq3555 eq3834
    | exact resolve eq3834 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3834
  have eq3922 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) X2)))))))))) = (M.op (M.op x y) (M.op X1 (M.op X0 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y X2)))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3555 eq3835
    | exact resolve eq3835 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3835
  have eq3963 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X1))))))))))))))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3885 X0 X1
       have i₂ := eq3792 sF0 x (M.op sF0 (M.op y (M.op sF0 (M.op y X1))))
       grind)
    | exact superpose eq3792 eq3885
    | exact resolve eq3885 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3885
  have eq3976 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x (M.op (M.op x y) X0)))) = (M.op (M.op x y) (M.op (σ y) (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op X2 X1) (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0)))))))))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq2888 eq3899
    | exact resolve eq3899 eq2888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2888 eq3899
  have eq3987 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op (M.op x y) (M.op y (M.op (M.op X2 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3)))))))))))))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3911 X0 X1 X2 X3
       have i₂ := eq1263 y sF0 y (M.op sF0 (M.op y (M.op (M.op X2 (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y (M.op X1 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y X3)))))))))))))) (M.op sF0 (M.op y (M.op sF0 (M.op y X0)))))))
       grind)
    | exact superpose eq1263 eq3911
    | exact resolve eq3911 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3911
  have eq3988 : ∀ X0 X1 X3 : G, (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))) = (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y X0))))))))))) := by
    intro X0 X1 X3
    first
    | exact superpose eq3555 eq3912
    | exact resolve eq3912 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3912
  have eq3997 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) X1)))))))))) = (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X1)))))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3921 x X1
       have i₂ := eq3792 sF0 x (M.op sF0 (M.op y X1))
       grind)
    | exact superpose eq3792 eq3921
    | exact resolve eq3921 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3921
  have eq3998 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X1 (M.op X0 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y X2)))))))))) = (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) X2)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3555 eq3922
    | exact resolve eq3922 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3922
  have eq4024 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op x (M.op (M.op x y) (M.op y (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X1)))))))))))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq3685 eq3963
    | exact resolve eq3963 eq3685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3963
  have eq4032 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x (M.op (M.op x y) X0)))) = (M.op (M.op x y) (M.op (σ y) (M.op (M.op X2 X1) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0)))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3601 eq3976
    | exact resolve eq3976 eq3601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3601 eq3976
  have eq4041 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3))))))))))))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0)))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3987 X0 X1 X0 X3
       have i₂ := eq3792 X0 (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y (M.op X1 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y X3))))))))))))) (M.op sF0 (M.op y (M.op sF0 (M.op y X0))))
       grind)
    | exact superpose eq3792 eq3987
    | exact resolve eq3987 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3987
  have eq4042 : ∀ X0 X1 X3 : G, (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y X0))))) = (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y X0))))))))))) := by
    intro X0 X1 X3
    first
    | exact superpose eq3555 eq3988
    | exact resolve eq3988 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3988
  have eq4054 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) X1)))))))))) = (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op x (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X1))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq3685 eq3997
    | exact resolve eq3997 eq3685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3997
  have eq4073 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op x (M.op x (M.op (M.op x y) (M.op y (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X1))))))))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq1363 eq4024
    | exact resolve eq4024 eq1363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4024
  have eq4079 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x (M.op (M.op x y) X0)))) = (M.op (M.op x y) (M.op y (M.op (M.op X2 X1) (M.op (M.op x y) X0)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3998 eq4032
    | exact resolve eq4032 eq3998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4032
  have eq4087 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3)))))))))))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4041 X0 X1 X2 X3
       have i₂ := eq3792 sF0 (M.op y (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y (M.op X1 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y X3)))))))))))) (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op y X0))))))
       grind)
    | exact superpose eq3792 eq4041
    | exact resolve eq4041 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4041
  have eq4096 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) X1)))))))))) = (M.op (M.op x y) (M.op x (M.op x (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X1)))))))))) := by
    intro X0 X1
    first
    | exact superpose eq1363 eq4054
    | exact resolve eq4054 eq1363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4054
  have eq4103 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op x (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X1)))))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq156 eq4073
    | exact resolve eq4073 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4073
  have eq4108 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op x (M.op (M.op x y) X0)))) = (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (M.op x y) X0))))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4079 X0 X2 X0
       have i₂ := eq3792 X0 X2 (M.op sF0 X0)
       grind)
    | exact superpose eq3792 eq4079
    | exact resolve eq4079 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4079
  have eq4112 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op x (M.op (M.op x y) (M.op y (M.op (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3)))))))))))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0)))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq3685 eq4087
    | exact resolve eq4087 eq3685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4087
  have eq4120 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) X1)))))))))) = (M.op (M.op x y) (M.op x (M.op X0 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X1))))))) := by
    intro X0 X1
    first
    | exact superpose eq156 eq4096
    | exact resolve eq4096 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4096
  have eq4126 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X1))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq156 eq4103
    | exact resolve eq4103 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4103
  have eq4133 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op x (M.op x (M.op (M.op x y) (M.op y (M.op (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3)))))))))))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1363 eq4112
    | exact resolve eq4112 eq1363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363 eq4112
  have eq4140 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) X1)))) = (M.op (M.op x y) (M.op x (M.op X0 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X1))))))) := by
    intro X0 X1
    first
    | exact superpose eq3555 eq4120
    | exact resolve eq4120 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4120
  have eq4144 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op (M.op x y) (M.op y X1)))))))))) := by
    intro X0 X1
    first
    | exact superpose eq156 eq4126
    | exact resolve eq4126 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4126
  have eq4151 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op x (M.op (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3)))))))))))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0)))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq156 eq4133
    | exact resolve eq4133 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4133
  have eq4168 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3)))))))))))) (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq4140 eq4151
    | exact resolve eq4151 eq4140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4151
  have eq4174 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3))))))))))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0)))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4168 X0 X1 X2 X3
       have i₂ := eq3792 y (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y (M.op X1 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y X3))))))))))) (M.op sF0 (M.op sF0 (M.op y (M.op sF0 (M.op y X0)))))
       grind)
    | exact superpose eq3792 eq4168
    | exact resolve eq4168 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4168
  have eq4178 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op x (M.op (M.op x y) (M.op y (M.op (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3))))))))))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq4108 eq4174
    | exact resolve eq4174 eq4108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4174
  have eq4181 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3))))))))))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0)))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq156 eq4178
    | exact resolve eq4178 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4178
  have eq4184 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3)))))))))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4181 X0 X1 X2 X3
       have i₂ := eq3792 sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y (M.op X1 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y X3)))))))))) (M.op sF0 (M.op y (M.op sF0 (M.op sF0 (M.op y (M.op sF0 (M.op y X0)))))))
       grind)
    | exact superpose eq3792 eq4181
    | exact resolve eq4181 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4181
  have eq4187 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op x (M.op (M.op x y) (M.op y (M.op (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3)))))))))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0)))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq3685 eq4184
    | exact resolve eq4184 eq3685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4184
  have eq4190 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3)))))))))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq86 eq4187
    | exact resolve eq4187 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4187
  have eq4193 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3))))))))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0)))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4190 X0 X1 X2 X3
       have i₂ := eq3792 y (M.op sF3 (M.op sF0 (M.op y (M.op X1 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y X3))))))))) (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op sF0 (M.op y (M.op sF0 (M.op y X0)))))))))
       grind)
    | exact superpose eq3792 eq4190
    | exact resolve eq4190 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4190
  have eq4196 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3))))))))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0)))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4193 X0 X1 X2 X3
       have i₂ := eq1263 y sF0 y (M.op sF0 (M.op y (M.op (M.op sF3 (M.op sF0 (M.op y (M.op X1 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y X3))))))))) (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op sF0 (M.op y (M.op sF0 (M.op y X0))))))))))))))
       grind)
    | exact superpose eq1263 eq4193
    | exact resolve eq4193 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4193
  have eq4199 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3)))))))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4196 X0 X1 X2 X3
       have i₂ := eq3792 sF3 (M.op sF0 (M.op y (M.op X1 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y X3)))))))) (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op sF0 (M.op y (M.op sF0 (M.op y X0)))))))))))
       grind)
    | exact superpose eq3792 eq4196
    | exact resolve eq4196 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4196
  have eq4202 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3))))))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0)))))))))))))))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4199 X0 X1 X2 X3
       have i₂ := eq3792 sF0 (M.op y (M.op X1 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y X3))))))) (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op sF0 (M.op y (M.op sF0 (M.op y X0)))))))))))))
       grind)
    | exact superpose eq3792 eq4199
    | exact resolve eq4199 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4199
  have eq4205 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3))))))) (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq4108 eq4202
    | exact resolve eq4202 eq4108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4202
  have eq4208 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3)))))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0)))))))))))))))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4205 X0 X1 X2 X3
       have i₂ := eq3792 y (M.op X1 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y X3)))))) (M.op sF0 (M.op x (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op sF0 (M.op y (M.op sF0 (M.op y X0)))))))))))))))
       grind)
    | exact superpose eq3792 eq4205
    | exact resolve eq4205 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4205
  have eq4211 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op (σ y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3)))))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq4108 eq4208
    | exact resolve eq4208 eq4108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4208
  have eq4214 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op (σ y) (M.op (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3)))))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0)))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq156 eq4211
    | exact resolve eq4211 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4211
  have eq4217 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3))))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))))))))))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4214 X0 X0 X2 X3
       have i₂ := eq3792 X0 (M.op sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y X3))))) (M.op sF0 (M.op y (M.op sF0 (M.op x (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op sF0 (M.op y (M.op sF0 (M.op y X0)))))))))))))))))
       grind)
    | exact superpose eq3792 eq4214
    | exact resolve eq4214 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4214
  have eq4220 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3)))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0)))))))))))))))))))))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4217 X0 X1 X2 X3
       have i₂ := eq3792 sF0 (M.op y (M.op sF3 (M.op sF0 (M.op y X3)))) (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op x (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op sF0 (M.op y (M.op sF0 (M.op y X0)))))))))))))))))))
       grind)
    | exact superpose eq3792 eq4217
    | exact resolve eq4217 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4217
  have eq4223 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X3)))) (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))))))))))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq4108 eq4220
    | exact resolve eq4220 eq4108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4220
  have eq4226 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op (σ y) (M.op (M.op x y) (M.op y X3))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0)))))))))))))))))))))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4223 X0 X1 X2 X3
       have i₂ := eq3792 y (M.op sF3 (M.op sF0 (M.op y X3))) (M.op sF0 (M.op x (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op x (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op sF0 (M.op y (M.op sF0 (M.op y X0)))))))))))))))))))))
       grind)
    | exact superpose eq3792 eq4223
    | exact resolve eq4223 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4223
  have eq4229 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op (σ y) (M.op (M.op x y) (M.op y X3))) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0)))))))))))))))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq3998 eq4226
    | exact resolve eq4226 eq3998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3998 eq4226
  have eq4232 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op (M.op x y) (M.op y X3)) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))))))))))))))))))))))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4229 X0 X1 X2 X3
       have i₂ := eq3792 sF3 (M.op sF0 (M.op y X3)) (M.op sF0 (M.op y (M.op sF0 (M.op x (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op x (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op sF0 (M.op y (M.op sF0 (M.op y X0)))))))))))))))))))))))
       grind)
    | exact superpose eq3792 eq4229
    | exact resolve eq4229 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4229
  have eq4235 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op y X3) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0)))))))))))))))))))))))))))))))))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4232 X0 X1 X2 X3
       have i₂ := eq3792 sF0 (M.op y X3) (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op x (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op x (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op sF0 (M.op y (M.op sF0 (M.op y X0)))))))))))))))))))))))))
       grind)
    | exact superpose eq3792 eq4232
    | exact resolve eq4232 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4232
  have eq4238 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op y X3) (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))))))))))))))))))))))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq4108 eq4235
    | exact resolve eq4235 eq4108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4235
  have eq4241 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0)))))))))))))))))))))))))))))))))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4238 X0 X1 X2 X2
       have i₂ := eq3792 y X2 (M.op sF0 (M.op x (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op x (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op x (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op y (M.op sF0 (M.op sF0 (M.op y (M.op sF0 (M.op y X0)))))))))))))))))))))))))))
       grind)
    | exact superpose eq3792 eq4238
    | exact resolve eq4238 eq3792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4238
  have eq4244 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op x (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))))))))))))))))))))))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq4108 eq4241
    | exact resolve eq4241 eq4108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4108 eq4241
  have eq4247 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op X1 (M.op x (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))))))))))))))))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq3555 eq4244
    | exact resolve eq4244 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3555 eq4244
  have eq4250 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op X1 (M.op X3 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0)))))))))))))))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq156 eq4247
    | exact resolve eq4247 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4247
  have eq4253 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op X1 (M.op X3 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))))))))))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq156 eq4250
    | exact resolve eq4250 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4250
  have eq4256 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op X1 (M.op X3 (M.op y (M.op x (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0)))))))))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq3685 eq4253
    | exact resolve eq4253 eq3685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4253
  have eq4259 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op X1 (M.op X3 (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq86 eq4256
    | exact resolve eq4256 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4256
  have eq4262 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op X1 (M.op X3 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0)))))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq156 eq4259
    | exact resolve eq4259 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4259
  have eq4265 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op X1 (M.op X3 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq156 eq4262
    | exact resolve eq4262 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4262
  have eq4268 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op X1 (M.op X3 (M.op y (M.op x (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0)))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq3685 eq4265
    | exact resolve eq4265 eq3685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4265
  have eq4271 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op X1 (M.op X3 (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y X0))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq86 eq4268
    | exact resolve eq4268 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4268
  have eq4274 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op X1 (M.op X3 (M.op y (M.op y (M.op x (M.op (M.op x y) (M.op y X0)))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq3685 eq4271
    | exact resolve eq4271 eq3685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4271
  have eq4277 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y X0))))))))))))) = (M.op y (M.op X2 (M.op y (M.op X1 (M.op X3 (M.op y (M.op y X0))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq86 eq4274
    | exact resolve eq4274 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4274
  have eq4280 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op X2 (M.op y (M.op X1 (M.op X3 (M.op y (M.op y X0))))))) = (M.op X1 (M.op X2 (M.op (M.op x y) (M.op y (M.op X3 (M.op (M.op x y) (M.op y X0))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq4042 eq4277
    | exact resolve eq4277 eq4042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4042 eq4277
  have eq4298 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op (σ y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X1 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y X0))))))))))))))))))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq4280 eq3863
    | exact resolve eq3863 eq4280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3863
  have eq4328 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 (M.op X2 X3)))) = (M.op (M.op x y) (M.op y (M.op X0 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op X1 (M.op y (M.op y X3)))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq4280 eq3789
    | exact resolve eq3789 eq4280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3789
  have eq4331 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op x y) (M.op y (M.op X0 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op X2 (M.op y (M.op y X3)))))))))) := by
    intro X0 X2 X3
    first
    | exact superpose eq4280 eq3792
    | exact resolve eq3792 eq4280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3792
  have eq4391 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X1 (M.op X1 X0)))) = (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (τ (M.op X1 X0)) (M.op y (M.op y (τ (M.op X1 X0))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3684 X0 X1
       have i₂ := eq4328 sF0 (τ (M.op X1 X0)) y (τ (M.op X1 X0))
       grind)
    | exact superpose eq4328 eq3684
    | exact resolve eq3684 eq4328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3684
  have eq4392 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ x) (M.op y (M.op y X0))))))))))) := by
    intro X0
    first
    | (have i₁ := eq3686 x
       have i₂ := eq4328 sF0 sF2 y x
       grind)
    | exact superpose eq4328 eq3686
    | exact resolve eq3686 eq4328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3686
  have eq4420 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op x y) (M.op y (M.op X1 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op X2 (M.op (M.op x y) (M.op y (M.op (M.op x y) (M.op y (M.op X1 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y X0))))))))))))))))))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq4280 eq4298
    | exact resolve eq4298 eq4280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4298
  have eq4456 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op x y) (M.op y (M.op X1 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y (M.op y (M.op y (M.op X2 (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op X1 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y X0))))))))))))))))))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq4280 eq4420
    | exact resolve eq4420 eq4280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4280 eq4420
  have eq4531 : ∀ X0 : G, (M.op x (M.op x (M.op (M.op x y) X0))) = (M.op y (M.op (M.op x y) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq156 eq2776
    | exact resolve eq2776 eq156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq4533 : ∀ X0 : G, (M.op y (M.op y (M.op x X0))) = (M.op (M.op x y) (M.op x (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq52 eq2776
    | exact resolve eq2776 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4537 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op (M.op x y) X0))) = (M.op x (M.op x (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq2776 eq2776
    | exact resolve eq2776 eq2776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4540 : ∀ X0 : G, (M.op (M.op x y) (M.op y (M.op y X0))) = (M.op x (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq2776 eq52
    | exact resolve eq52 eq2776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4541 : ∀ X0 : G, (M.op y (M.op x (M.op y X0))) = (M.op x (M.op (M.op x y) (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq2776 eq86
    | exact resolve eq86 eq2776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq2776
  have eq4545 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y (M.op x (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) (M.op (M.op x y) (M.op y X1)))))))))) := by
    intro X0 X1
    first
    | exact superpose eq4541 eq4144
    | exact resolve eq4144 eq4541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4144 eq4541
  have eq4565 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op x (M.op (M.op x y) (M.op x (M.op y (M.op (M.op x y) (M.op (σ x) (M.op y (M.op y X0))))))))))) := by
    intro X0
    first
    | exact superpose eq4540 eq4392
    | exact resolve eq4392 eq4540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4392
  have eq4588 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X1 (M.op X1 X0)))) = (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op x (M.op (M.op x y) (M.op x (M.op y (M.op (M.op x y) (M.op (τ (M.op X1 X0)) (M.op y (M.op y (τ (M.op X1 X0))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq4540 eq4391
    | exact resolve eq4391 eq4540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4391
  have eq4590 : ∀ X0 : G, (M.op x (M.op (M.op x y) X0)) = (M.op x (M.op (M.op x y) (M.op x (M.op (M.op x y) (M.op y X0))))) := by
    intro X0
    first
    | exact superpose eq4540 eq1386
    | exact resolve eq1386 eq4540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386 eq4540
  have eq4594 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op (M.op x y) (M.op x (M.op x (M.op y (M.op y X0))))) := by
    intro X0
    first
    | exact superpose eq4537 eq3685
    | exact resolve eq3685 eq4537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3685
  have eq4596 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) X1)))) = (M.op (M.op x y) (M.op x (M.op X0 (M.op (M.op x y) (M.op x (M.op x (M.op (M.op x y) X1))))))) := by
    intro X0 X1
    first
    | exact superpose eq4531 eq4140
    | exact resolve eq4140 eq4531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4140
  have eq4611 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op x y) (M.op y (M.op X1 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y (M.op y (M.op y (M.op X2 (M.op y (M.op x (M.op x (M.op (M.op x y) (M.op X1 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y X0))))))))))))))))))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq4531 eq4456
    | exact resolve eq4456 eq4531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4456
  have eq4619 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y (M.op x (M.op y (M.op x (M.op x (M.op (M.op x y) (M.op X0 (M.op (M.op x y) (M.op (M.op x y) (M.op y X1)))))))))) := by
    intro X0 X1
    first
    | exact superpose eq4531 eq4545
    | exact resolve eq4545 eq4531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4545
  have eq4622 : ∀ X0 : G, (M.op x (M.op (M.op x y) X0)) = (M.op x (M.op y (M.op y (M.op x (M.op y X0))))) := by
    intro X0
    first
    | exact superpose eq4533 eq4590
    | exact resolve eq4590 eq4533
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4533 eq4590
  have eq4624 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X1 (M.op X1 X0)))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x (M.op y (M.op (M.op x y) (M.op (τ (M.op X1 X0)) (M.op y (M.op y (τ (M.op X1 X0)))))))))) := by
    intro X0 X1
    first
    | exact superpose eq52 eq4588
    | exact resolve eq4588 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4588
  have eq4647 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op x y) (M.op (M.op x y) (M.op x (M.op y (M.op (M.op x y) (M.op (σ x) (M.op y (M.op y X0)))))))) := by
    intro X0
    first
    | exact superpose eq52 eq4565
    | exact resolve eq4565 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4565
  have eq4673 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op y X0))) = (M.op x (M.op x (M.op y (M.op y (M.op x (M.op y X0)))))) := by
    intro X0
    first
    | exact superpose eq4622 eq4531
    | exact resolve eq4531 eq4622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4531
  have eq4676 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) X1)))) = (M.op (M.op x y) (M.op x (M.op X0 (M.op (M.op x y) (M.op x (M.op x (M.op y (M.op y (M.op x (M.op y X1)))))))))) := by
    intro X0 X1
    first
    | exact superpose eq4622 eq4596
    | exact resolve eq4596 eq4622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4596
  have eq4682 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op x y) (M.op y (M.op X1 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y (M.op y (M.op y (M.op X2 (M.op y (M.op x (M.op x (M.op y (M.op y (M.op x (M.op y (M.op X1 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y X0)))))))))))))))))))))))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq4622 eq4611
    | exact resolve eq4611 eq4622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4611
  have eq4690 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y (M.op x (M.op y (M.op x (M.op x (M.op y (M.op y (M.op x (M.op y (M.op X0 (M.op (M.op x y) (M.op (M.op x y) (M.op y X1))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq4622 eq4619
    | exact resolve eq4619 eq4622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4619
  have eq4741 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) X1)))) = (M.op (M.op x y) (M.op x (M.op X0 (M.op y (M.op x (M.op x (M.op y X1))))))) := by
    intro X0 X1
    first
    | exact superpose eq4594 eq4676
    | exact resolve eq4676 eq4594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4594 eq4676
  have eq5276 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op x y) (M.op y (M.op X0 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y (M.op y (M.op y (M.op x (M.op y (M.op y (M.op x (M.op y (M.op X0 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y X1))))))))))))))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq52 eq4682
    | exact resolve eq4682 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4682
  have eq5285 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op x y) (M.op y (M.op X0 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y (M.op y (M.op X0 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y X1))))))))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq5276 X0 X1
       have i₂ := eq1263 x y y (M.op y (M.op X0 (M.op y (M.op y (M.op y (M.op sF0 (M.op sF3 (M.op y (M.op y X1)))))))))
       grind)
    | exact superpose eq1263 eq5276
    | exact resolve eq5276 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5276
  have eq12568 : ∀ X0 X1 : G, y = (M.op X0 (M.op X1 (M.op x (M.op X0 (M.op X1 (M.op x y)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1263 x X1 X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1263
    | (have j0 := eq1263 x X1 X0 y
       grind)
    | exact resolve eq1263 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12569 : ∀ X0 X1 X2 : G, (M.op y (M.op x X0)) = (M.op X1 (M.op X2 (M.op (M.op x y) (M.op X1 (M.op X2 X0))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq1263
    | exact resolve eq1263 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12573 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op X1 (M.op (σ x) (M.op X0 (M.op X1 (M.op (σ x) (σ y))))))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq1263
    | (have j0 := eq1263 (σ x) X1 X0 (σ y)
       grind)
    | exact resolve eq1263 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12575 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op (M.op x y) (M.op y (M.op X1 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq52 eq1263
    | exact resolve eq1263 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12596 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op X1 (M.op y (M.op x (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X1 (M.op y (M.op x (M.op X1 X0))))
       have i₂ := eq1263 X1 x y X0
       grind)
    | exact superpose eq1263 eq52
    | exact resolve eq52 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13180 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op X1 (M.op X2 (M.op (σ x) (σ y))))) = (M.op X0 (M.op X1 (M.op X2 (M.op X0 (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq12573 eq1263
    | exact resolve eq1263 eq12573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13603 : ∀ X0 : G, (M.op x (M.op y (M.op x X0))) = (M.op (M.op x y) (M.op (M.op x y) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq52 eq12575
    | exact resolve eq12575 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13611 : ∀ X0 : G, (M.op x (M.op y (M.op y X0))) = (M.op (M.op x y) (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq12575 eq12575
    | exact resolve eq12575 eq12575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13620 : ∀ X0 X1 X2 : G, (M.op y (M.op X2 X0)) = (M.op X1 (M.op X2 (M.op (M.op x y) (M.op X1 (M.op x X0))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq12575 eq1263
    | exact resolve eq1263 eq12575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13625 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x y) (M.op y (M.op X3 X0))) = (M.op X1 (M.op X2 (M.op X3 (M.op X1 (M.op X2 (M.op x X0)))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq12575 eq1263
    | exact resolve eq1263 eq12575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13661 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op x (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ x) (M.op y (M.op y X0)))))))) := by
    intro X0
    first
    | exact superpose eq13611 eq4647
    | exact resolve eq4647 eq13611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4647
  have eq13694 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X1 (M.op X1 X0)))) = (M.op x (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (τ (M.op X1 X0)) (M.op y (M.op y (τ (M.op X1 X0)))))))))) := by
    intro X0 X1
    first
    | exact superpose eq13611 eq4624
    | exact resolve eq4624 eq13611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4624
  have eq13701 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op y (M.op x (M.op y (M.op x (M.op x (M.op y (M.op y (M.op x (M.op y (M.op X0 (M.op x (M.op y (M.op x X1))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq13603 eq4690
    | exact resolve eq4690 eq13603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4690
  have eq14368 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op X1 X0)))) = (M.op X1 (M.op y (M.op x (M.op x X0)))) := by
    intro X0 X1
    first
    | exact superpose eq12575 eq12596
    | exact resolve eq12596 eq12575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14378 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X1 (M.op x (M.op X2 (M.op X1 X0))))) = (M.op X2 (M.op y X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12596 (M.op X1 (M.op x (M.op X2 (M.op X1 X0)))) X2
       have i₂ := eq1263 X1 X2 x X0
       grind)
    | exact superpose eq1263 eq12596
    | exact resolve eq12596 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14389 : ∀ X0 X1 X2 : G, (M.op x X2) = (M.op X1 (M.op X0 (M.op y (M.op x (M.op X0 (M.op y (M.op X1 X2))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq12596 eq12575
    | exact resolve eq12575 eq12596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14428 : ∀ X0 X1 X2 : G, (M.op x (M.op X2 X0)) = (M.op X1 (M.op X2 (M.op y (M.op X1 (M.op (M.op x y) X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1263 y X2 X1 (M.op x (M.op X2 X0))
       have i₂ := eq12596 X0 X2
       grind)
    | exact superpose eq12596 eq1263
    | exact resolve eq1263 eq12596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14433 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op x (M.op X3 X0))) = (M.op X1 (M.op X2 (M.op X3 (M.op X1 (M.op X2 (M.op (M.op x y) X0)))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1263 X3 X2 X1 (M.op y (M.op x (M.op X3 X0)))
       have i₂ := eq12596 X0 X3
       grind)
    | exact superpose eq12596 eq1263
    | exact resolve eq1263 eq12596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14502 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op x (M.op y (M.op X0 (M.op x (M.op y (M.op x X1))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq13701 X0 X1
       have i₂ := eq14389 x y (M.op x (M.op y (M.op X0 (M.op x (M.op y (M.op x X1))))))
       grind)
    | exact superpose eq14389 eq13701
    | exact resolve eq13701 eq14389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13701 eq14389
  have eq14509 : ∀ X0 X1 : G, (M.op X1 (M.op y (M.op x (M.op x X0)))) = (M.op x (M.op y (M.op x (M.op X1 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq13603 eq14368
    | exact resolve eq14368 eq13603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14368
  have eq18435 : ∀ X0 : G, (M.op x (M.op x (M.op y (M.op (M.op x y) (M.op y (M.op (M.op x y) X0)))))) = (M.op y (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq12575 eq4537
    | exact resolve eq4537 eq12575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18441 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op x (M.op y (M.op y (M.op (M.op x y) X0))))) := by
    intro X0
    first
    | exact superpose eq12575 eq4537
    | exact resolve eq4537 eq12575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18476 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op x X0))) = (M.op x (M.op x (M.op x (M.op x (M.op y (M.op y (M.op x (M.op y (M.op (M.op x y) X0))))))))) := by
    intro X0
    first
    | exact superpose eq4673 eq18435
    | exact resolve eq18435 eq4673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18435
  have eq18491 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op x X0))) = (M.op x (M.op x (M.op x (M.op y (M.op x (M.op y X0)))))) := by
    intro X0
    first
    | exact superpose eq14433 eq18476
    | exact resolve eq18476 eq14433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14433 eq18476
  have eq19565 : ∀ X0 : G, (M.op y (M.op x (M.op y (M.op x X0)))) = (M.op x (M.op x (M.op y (M.op y X0)))) := by
    intro X0
    first
    | exact superpose eq13603 eq4537
    | exact resolve eq4537 eq13603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4537
  have eq19568 : ∀ X0 X1 : G, (M.op x (M.op y (M.op x X0))) = (M.op X1 (M.op y (M.op x (M.op X1 (M.op (M.op x y) (M.op y X0)))))) := by
    intro X0 X1
    first
    | exact superpose eq13603 eq12596
    | exact resolve eq12596 eq13603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20419 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op x X0)) = (M.op X1 (M.op X2 (M.op (M.op x y) (M.op X1 (M.op X2 (M.op x (M.op y (M.op y X0)))))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq13611 eq1263
    | exact resolve eq1263 eq13611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13611
  have eq20427 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op y (M.op x (M.op x (M.op y (M.op y X0))))) := by
    intro X0
    first
    | exact superpose eq12569 eq20419
    | exact resolve eq20419 eq12569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12569 eq20419
  have eq20449 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y (M.op X0 (M.op (M.op x y) X1)))) = (M.op y (M.op x (M.op x (M.op y (M.op y (M.op X0 (M.op y (M.op x (M.op x (M.op y X1)))))))))) := by
    intro X0 X1
    first
    | exact superpose eq20427 eq4741
    | exact resolve eq4741 eq20427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4741
  have eq20489 : ∀ X0 : G, (M.op x (M.op x (M.op x (M.op y (M.op x (M.op y X0)))))) = (M.op y (M.op y (M.op x (M.op x (M.op y (M.op y X0)))))) := by
    intro X0
    first
    | exact superpose eq20427 eq18491
    | exact resolve eq18491 eq20427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18491
  have eq20504 : ∀ X0 : G, (M.op x (M.op x (M.op x (M.op y (M.op x (M.op y X0)))))) = (M.op x (M.op y (M.op x (M.op y (M.op y (M.op y X0)))))) := by
    intro X0
    first
    | (have i₁ := eq20489 X0
       have i₂ := eq14509 (M.op y (M.op y X0)) y
       grind)
    | exact superpose eq14509 eq20489
    | exact resolve eq20489 eq14509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20489
  have eq22473 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq346
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq346
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq346 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22509 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22473
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22473
    | exact resolve eq22473 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22473
  have eq22512 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq22509
    | exact resolve eq22509 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22509
  have eq22513 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22512
       have r₂ := eq27
       grind)
    | exact resolve eq22512 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22512
  have eq22514 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq22513
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22513
    | exact resolve eq22513 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22513
  have eq22534 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op X1 (M.op (σ y) (M.op X0 (M.op X1 (M.op (σ y) (σ x))))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op y x) = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq22514 eq1263
    | exact resolve eq1263 eq22514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22514
  have eq22545 : (M.op y x) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22534 x x
       have i₂ := eq1263 sF3 x x sF2
       grind)
    | exact superpose eq1263 eq22534
    | exact resolve eq22534 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22534
  have eq22571 : (M.op x (M.op y (M.op x y))) = (M.op (M.op x y) (M.op (M.op x y) (M.op y x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13603 y
       have i₂ := eq22545
       grind)
    | exact superpose eq22545 eq13603
    | exact resolve eq13603 eq22545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22584 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op y (M.op y x)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12575 y y
       have i₂ := eq22545
       grind)
    | exact superpose eq22545 eq12575
    | exact resolve eq12575 eq22545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22545
  have eq22587 : (M.op x y) = (M.op x (M.op x (M.op y (M.op y (M.op x (M.op y (M.op y x))))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq4673 eq22584
    | exact resolve eq22584 eq4673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22584
  have eq22597 : (M.op x (M.op y (M.op x y))) = (M.op x (M.op y (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq13603 eq22571
    | exact resolve eq22571 eq13603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13603 eq22571
  have eq22598 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22587
       have i₂ := eq1263 y y x x
       grind)
    | exact superpose eq1263 eq22587
    | exact resolve eq22587 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22587
  have eq22602 : (M.op x (M.op y (M.op x y))) = (M.op x (M.op y (M.op x x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22597
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22597
    | exact resolve eq22597 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22597
  have eq22603 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22598
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq22598
    | exact resolve eq22598 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22598
  have eq24655 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq327 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq327
    | exact resolve eq327 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq24823 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24655 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq24655
    | (have j0 := eq24655 X0 X1
       grind)
    | exact resolve eq24655 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24655
  have eq42519 : ∀ X0 X1 : G, (M.op y (M.op x x)) = (M.op X0 (M.op X1 (M.op x (M.op X0 (M.op X1 (M.op x (M.op y (M.op x y)))))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq1263 x X1 X0 (M.op y (M.op x x))
       have i₂ := eq22602
       grind)
    | exact superpose eq22602 eq1263
    | exact resolve eq1263 eq22602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22602
  have eq42526 : (M.op y (M.op x y)) = (M.op y (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq42519 x x
       have i₂ := eq1263 x x x (M.op y sF0)
       grind)
    | exact superpose eq1263 eq42519
    | exact resolve eq42519 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42519
  have eq42732 : (M.op x (M.op x x)) = (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op x y))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12575 (M.op x x) y
       have i₂ := eq42526
       grind)
    | exact superpose eq42526 eq12575
    | exact resolve eq12575 eq42526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42526
  have eq42733 : (M.op x (M.op x x)) = (M.op x (M.op x (M.op y (M.op y (M.op x (M.op y (M.op y (M.op x y)))))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq4673 eq42732
    | exact resolve eq42732 eq4673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4673 eq42732
  have eq42748 : (M.op x (M.op x y)) = (M.op x (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq42733
       have i₂ := eq1263 y y x sF0
       grind)
    | exact superpose eq1263 eq42733
    | exact resolve eq42733 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42733
  have eq42875 : ∀ X0 : G, (M.op x X0) ≠ (M.op x (M.op (M.op x x) (M.op x (M.op x y)))) ∨ (M.op x X0) = (k X0 (M.op (M.op x x) (M.op x (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq396 x (M.op x x) x
       have i₂ := eq42748
       grind)
    | exact superpose eq42748 eq396
    | exact resolve eq396 eq42748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396 eq42748
  have eq42885 : ∀ X0 : G, (M.op x X0) ≠ (M.op x (M.op (M.op x y) (M.op y (M.op x (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op x (M.op y (M.op y (M.op x (M.op x y))))))))))))) ∨ (M.op x X0) = (k X0 (M.op (M.op x x) (M.op x (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq42875 X0
       have i₂ := eq4331 x x (M.op x sF0)
       grind)
    | exact superpose eq4331 eq42875
    | (have j0 := eq42875 X0
       grind)
    | exact resolve eq42875 eq4331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42875
  have eq42895 : ∀ X0 : G, (M.op x X0) ≠ (M.op x (M.op y (M.op y (M.op x (M.op y (M.op y (M.op x (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op x (M.op y (M.op y (M.op x (M.op x y)))))))))))))))) ∨ (M.op x X0) = (k X0 (M.op (M.op x x) (M.op x (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq4622 eq42885
    | (have j0 := eq42885 X0
       grind)
    | (have r₁ := eq42885 (M.op y (M.op y (M.op x (M.op y (M.op y (M.op x (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op x (M.op y (M.op y (M.op x (M.op x y)))))))))))))))
       have r₂ := eq4622 (M.op y (M.op x (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op x (M.op y (M.op y (M.op x (M.op x y)))))))))))
       grind)
    | exact resolve eq42885 eq4622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4622 eq42885
  have eq42903 : ∀ X0 : G, (M.op x X0) ≠ (M.op x (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op x (M.op y (M.op y (M.op x (M.op x y)))))))))) ∨ (M.op x X0) = (k X0 (M.op (M.op x x) (M.op x (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq42895 X0
       have i₂ := eq1263 y y x (M.op x (M.op y (M.op y (M.op y (M.op sF0 (M.op x (M.op y (M.op y (M.op x sF0)))))))))
       grind)
    | exact superpose eq1263 eq42895
    | (have j0 := eq42895 X0
       grind)
    | (have r₁ := eq42895 (M.op x (M.op X0 (M.op x (M.op x (M.op X0 (M.op x (M.op y (M.op y (M.op x (M.op y (M.op y (M.op x (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op x (M.op y (M.op y (M.op x (M.op x y)))))))))))))))))))))
       have r₂ := eq1263 X0 x x (M.op x (M.op y (M.op y (M.op x (M.op y (M.op y (M.op x (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op x (M.op y (M.op y (M.op x (M.op x y))))))))))))))))
       grind)
    | (have r₁ := eq42895 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op x (M.op y (M.op y (M.op x (M.op x y)))))))))
       have r₂ := eq1263 y y x (M.op x (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op x (M.op y (M.op y (M.op x (M.op x y))))))))))
       grind)
    | exact resolve eq42895 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42895
  have eq42911 : ∀ X0 : G, (M.op x X0) ≠ (M.op x (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x y))))))))))))) ∨ (M.op x X0) = (k X0 (M.op (M.op x x) (M.op x (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq20427 eq42903
    | (have j0 := eq42903 X0
       grind)
    | exact resolve eq42903 eq20427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42903
  have eq42919 : ∀ X0 : G, (M.op x X0) ≠ (M.op x (M.op y (M.op y (M.op x (M.op y (M.op x (M.op y (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x y))))))))))))) ∨ (M.op x X0) = (k X0 (M.op (M.op x x) (M.op x (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq42911 X0
       have i₂ := eq14509 (M.op y (M.op y (M.op y (M.op y (M.op x sF0))))) y
       grind)
    | exact superpose eq14509 eq42911
    | (have j0 := eq42911 X0
       grind)
    | exact resolve eq42911 eq14509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42911
  have eq42927 : ∀ X0 : G, (M.op x X0) ≠ (M.op x (M.op y (M.op x (M.op x (M.op y (M.op y (M.op y (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x y))))))))))))) ∨ (M.op x X0) = (k X0 (M.op (M.op x x) (M.op x (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq42919 X0
       have i₂ := eq19565 (M.op y (M.op y (M.op y (M.op y (M.op y (M.op x sF0))))))
       grind)
    | exact superpose eq19565 eq42919
    | (have j0 := eq42919 X0
       grind)
    | exact resolve eq42919 eq19565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42919
  have eq42935 : ∀ X0 : G, (M.op x X0) ≠ (M.op x (M.op y (M.op x (M.op x (M.op y (M.op x (M.op x y))))))) ∨ (M.op x X0) = (k X0 (M.op (M.op x x) (M.op x (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq42927 X0
       have i₂ := eq1263 y y y (M.op y (M.op x sF0))
       grind)
    | exact superpose eq1263 eq42927
    | (have j0 := eq42927 X0
       grind)
    | (have r₁ := eq42927 (M.op x (M.op X0 (M.op x (M.op x (M.op X0 (M.op x (M.op y (M.op x (M.op x (M.op y (M.op y (M.op y (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x y))))))))))))))))))
       have r₂ := eq1263 X0 x x (M.op x (M.op y (M.op x (M.op x (M.op y (M.op y (M.op y (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x y)))))))))))))
       grind)
    | exact resolve eq42927 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42927
  have eq42940 : ∀ X0 : G, (M.op x y) ≠ (M.op x X0) ∨ (M.op x X0) = (k X0 (M.op (M.op x x) (M.op x (M.op x y)))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq42935 X0
       have i₂ := eq1263 x y x sF0
       grind)
    | exact superpose eq1263 eq42935
    | (have j0 := eq42935 X0
       grind)
    | (have r₁ := eq42935 (M.op x (M.op X0 (M.op x (M.op x (M.op X0 (M.op x (M.op y (M.op x (M.op x (M.op y (M.op x (M.op x y))))))))))))
       have r₂ := eq1263 X0 x x (M.op x (M.op y (M.op x (M.op x (M.op y (M.op x (M.op x y)))))))
       grind)
    | (have r₁ := eq42935 y
       have r₂ := eq1263 x y x (M.op x y)
       grind)
    | exact resolve eq42935 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42935
  have eq42945 : ∀ X0 : G, (M.op x X0) = (k X0 (M.op (M.op x y) (M.op y (M.op x (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op x (M.op y (M.op y (M.op x (M.op x y))))))))))))) ∨ (M.op x y) ≠ (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq42940 X0
       have i₂ := eq4331 x x (M.op x sF0)
       grind)
    | exact superpose eq4331 eq42940
    | (have j0 := eq42940 X0
       grind)
    | exact resolve eq42940 eq4331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42940
  have eq42950 : ∀ X0 : G, (M.op x X0) = (k X0 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op x (M.op y (M.op y (M.op x (M.op x y)))))))))) ∨ (M.op x y) ≠ (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq52 eq42945
    | (have j0 := eq42945 X0
       grind)
    | exact resolve eq42945 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42945
  have eq42955 : ∀ X0 : G, (M.op x X0) = (k X0 (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x y))))))))))))) ∨ (M.op x y) ≠ (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq20427 eq42950
    | (have j0 := eq42950 X0
       grind)
    | exact resolve eq42950 eq20427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42950
  have eq42960 : ∀ X0 : G, (M.op x X0) = (k X0 (M.op y (M.op y (M.op x (M.op y (M.op x (M.op y (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x y))))))))))))) ∨ (M.op x y) ≠ (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq42955 X0
       have i₂ := eq14509 (M.op y (M.op y (M.op y (M.op y (M.op x sF0))))) y
       grind)
    | exact superpose eq14509 eq42955
    | (have j0 := eq42955 X0
       grind)
    | exact resolve eq42955 eq14509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42955
  have eq42965 : ∀ X0 : G, (M.op x X0) = (k X0 (M.op y (M.op x (M.op x (M.op y (M.op y (M.op y (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x y))))))))))))) ∨ (M.op x y) ≠ (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq42960 X0
       have i₂ := eq19565 (M.op y (M.op y (M.op y (M.op y (M.op y (M.op x sF0))))))
       grind)
    | exact superpose eq19565 eq42960
    | (have j0 := eq42960 X0
       grind)
    | exact resolve eq42960 eq19565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42960
  have eq42970 : ∀ X0 : G, (M.op x X0) = (k X0 (M.op y (M.op x (M.op x (M.op y (M.op x (M.op x y))))))) ∨ (M.op x y) ≠ (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq42965 X0
       have i₂ := eq1263 y y y (M.op y (M.op x sF0))
       grind)
    | exact superpose eq1263 eq42965
    | (have j0 := eq42965 X0
       grind)
    | (have r₁ := eq42965 (M.op x (M.op X0 (M.op x (M.op x (M.op X0 (M.op x y))))))
       have r₂ := eq1263 X0 x x (M.op x y)
       grind)
    | exact resolve eq42965 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42965
  have eq42975 : ∀ X0 : G, (M.op x y) ≠ (M.op x X0) ∨ (k X0 y) = (M.op x X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq12568 eq42970
    | (have j0 := eq42970 X0
       grind)
    | exact resolve eq42970 eq12568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12568 eq42970
  have eq43191 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq42975 x
       have i₂ := eq22603
       grind)
    | exact superpose eq22603 eq42975
    | (have j0 := eq42975 y
       grind)
    | (have r₁ := eq42975 x
       have r₂ := eq22603
       grind)
    | exact resolve eq42975 eq22603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22603 eq42975
  have eq43205 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq43191
  have eq43206 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq43205
  have eq43216 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq346
       have i₂ := eq43206
       grind)
    | exact superpose eq43206 eq346
    | exact resolve eq346 eq43206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346 eq43206
  have eq43234 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq43216
  have eq43241 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq43234
    | exact resolve eq43234 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43234
  have eq43248 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq43241
       have r₂ := eq27
       grind)
    | exact resolve eq43241 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43241
  have eq43435 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op X1 (M.op (σ y) (M.op X0 (M.op X1 (M.op (σ y) (σ x))))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq43248 eq1263
    | exact resolve eq1263 eq43248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43248
  have eq43448 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq43435 x x
       have i₂ := eq1263 sF3 x x sF2
       grind)
    | exact superpose eq1263 eq43435
    | exact resolve eq43435 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43435
  have eq43449 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq43448
  have eq43465 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op X1 (M.op (σ x) (M.op X0 (M.op X1 (σ x)))))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq43449 eq12573
    | exact resolve eq12573 eq43449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43470 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op x (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ x) (M.op y (M.op y X0)))))))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq43449 eq13661
    | exact resolve eq13661 eq43449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13661
  have eq49633 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq43465 eq1263
    | exact resolve eq1263 eq43465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43465
  have eq49697 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) = (M.op X0 (M.op X1 (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq26 eq49633
    | (have j0 := eq49633 X0 X1
       grind)
    | exact resolve eq49633 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49633
  have eq71216 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X1 (M.op y (M.op y (M.op X1 X0))))) = (M.op (M.op x y) (M.op y (M.op X2 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y (M.op y (M.op X2 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ y) X0))))))))))))))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5285 X2 (M.op X1 (M.op y (M.op y (M.op X1 X0))))
       have i₂ := eq1263 X1 y y X0
       grind)
    | exact superpose eq1263 eq5285
    | exact resolve eq5285 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71221 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y X0)))) = (M.op (M.op x y) (M.op y (M.op X1 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y (M.op y (M.op X1 (M.op y (M.op y (M.op y (M.op (M.op x y) X0)))))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq5285 X0 (M.op sF3 (M.op y (M.op y x)))
       have i₂ := eq1263 y y sF3 x
       grind)
    | exact superpose eq1263 eq5285
    | exact resolve eq5285 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71233 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op x (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y (M.op y (M.op X1 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y X0))))))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq5285 eq12575
    | exact resolve eq12575 eq5285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71236 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op y (M.op X1 (M.op (M.op x y) X0)))) = (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y (M.op y (M.op X1 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y X0)))))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq5285 eq1263
    | exact resolve eq1263 eq5285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5285
  have eq71264 : ∀ X0 X1 : G, (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y (M.op y (M.op X1 (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y X0)))))))))))))))) = (M.op y (M.op x (M.op x (M.op y (M.op y (M.op X1 (M.op y (M.op x (M.op x (M.op y X0)))))))))) := by
    intro X0 X1
    first
    | exact superpose eq20449 eq71236
    | exact resolve eq71236 eq20449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20449 eq71236
  have eq71278 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op y (M.op y (M.op X1 X0))))) = (M.op (M.op x y) (M.op (σ y) (M.op y (M.op y (M.op (σ y) X0))))) := by
    intro X0 X1
    first
    | exact superpose eq71221 eq71216
    | exact resolve eq71216 eq71221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71216 eq71221
  have eq71307 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op x (M.op y (M.op x (M.op x (M.op y (M.op y (M.op X1 (M.op y (M.op x (M.op x (M.op y X0))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq71264 eq71233
    | exact resolve eq71233 eq71264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71233 eq71264
  have eq71322 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op y (M.op y (M.op X1 X0))))) = (M.op (M.op x y) (M.op (M.op x y) (M.op y (M.op y (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op y X0))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq71278 x X1
       have i₂ := eq4328 y y sF3 x
       grind)
    | exact superpose eq4328 eq71278
    | exact resolve eq71278 eq4328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71278
  have eq71356 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op x (M.op y (M.op x (M.op y (M.op x (M.op x (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x (M.op y X0)))))))))))))) := by
    intro X0
    first
    | exact superpose eq71307 eq18441
    | exact resolve eq18441 eq71307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18441
  have eq71398 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 (M.op X2 X3)))) = (M.op (M.op x y) (M.op y (M.op X0 (M.op y (M.op y (M.op x (M.op y (M.op x (M.op x (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x (M.op y (M.op X1 (M.op y (M.op y X3))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq71307 eq4328
    | exact resolve eq4328 eq71307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4328
  have eq71401 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op x y) (M.op y (M.op X0 (M.op y (M.op y (M.op x (M.op y (M.op x (M.op x (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x (M.op y (M.op X2 (M.op y (M.op y X3))))))))))))))))))) := by
    intro X0 X2 X3
    first
    | exact superpose eq71307 eq4331
    | exact resolve eq4331 eq71307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4331
  have eq72168 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X1 (M.op X1 X0)))) = (M.op x (M.op y (M.op y (M.op x (M.op y (M.op x (M.op x (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x (M.op y (M.op (τ (M.op X1 X0)) (M.op y (M.op y (τ (M.op X1 X0))))))))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq71307 eq13694
    | exact resolve eq13694 eq71307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13694
  have eq72268 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op x (M.op y (M.op y (M.op x (M.op y (M.op x (M.op x (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x (M.op y (M.op (σ x) (M.op y (M.op y X0))))))))))))))))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq71307 eq43470
    | exact resolve eq43470 eq71307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43470
  have eq72858 : (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) = (σ (M.op x (M.op y (M.op x (M.op x (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x (M.op y x)))))))))))) := by
    first
    | exact superpose eq71307 eq299
    | exact resolve eq299 eq71307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299
  have eq72904 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op y (M.op y (M.op X1 X0))))) = (M.op x (M.op y (M.op x (M.op x (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op x (M.op x (M.op y (M.op y (M.op y (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op y X0)))))))))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq71307 eq71322
    | exact resolve eq71322 eq71307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71322
  have eq72952 : (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) = (σ (M.op x (M.op y (M.op x (M.op x (M.op y (M.op y (M.op x (M.op y (M.op x (M.op y (M.op y x)))))))))))) := by
    first
    | (have i₁ := eq72858
       have i₂ := eq14509 (M.op y x) y
       grind)
    | exact superpose eq14509 eq72858
    | exact resolve eq72858 eq14509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72858
  have eq73468 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op x (M.op y (M.op x (M.op x (M.op y (M.op y (M.op x (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x (M.op y (M.op (σ x) (M.op y (M.op y X0))))))))))))))))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq72268 X0
       have i₂ := eq19565 (M.op x (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x (M.op y (M.op sF2 (M.op y (M.op y X0)))))))))))
       grind)
    | exact superpose eq19565 eq72268
    | exact resolve eq72268 eq19565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72268
  have eq73535 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X1 (M.op X1 X0)))) = (M.op x (M.op y (M.op x (M.op x (M.op y (M.op y (M.op x (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x (M.op y (M.op (τ (M.op X1 X0)) (M.op y (M.op y (τ (M.op X1 X0))))))))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq72168 X0 X1
       have i₂ := eq19565 (M.op x (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x (M.op y (M.op (τ (M.op X1 X0)) (M.op y (M.op y (τ (M.op X1 X0)))))))))))))
       grind)
    | exact superpose eq19565 eq72168
    | exact resolve eq72168 eq19565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72168
  have eq74243 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op x y) (M.op y (M.op X0 (M.op y (M.op x (M.op x (M.op y (M.op y (M.op x (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x (M.op y (M.op X2 (M.op y (M.op y X3))))))))))))))))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq71401 X0 X2 X3
       have i₂ := eq19565 (M.op x (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x (M.op y (M.op X2 (M.op y (M.op y X3)))))))))))
       grind)
    | exact superpose eq19565 eq71401
    | exact resolve eq71401 eq19565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71401
  have eq74246 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 (M.op X2 X3)))) = (M.op (M.op x y) (M.op y (M.op X0 (M.op y (M.op x (M.op x (M.op y (M.op y (M.op x (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x (M.op y (M.op X1 (M.op y (M.op y X3))))))))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq71398 X0 X1 X2 X3
       have i₂ := eq19565 (M.op x (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x (M.op y (M.op X1 (M.op y (M.op y X3)))))))))))
       grind)
    | exact superpose eq19565 eq71398
    | exact resolve eq71398 eq19565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71398
  have eq74287 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op x (M.op x (M.op x (M.op y (M.op y (M.op x (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x (M.op y X0)))))))))))))) := by
    intro X0
    first
    | (have i₁ := eq71356 X0
       have i₂ := eq19565 (M.op x (M.op y (M.op y (M.op y (M.op y (M.op x (M.op x (M.op y X0))))))))
       grind)
    | exact superpose eq19565 eq71356
    | exact resolve eq71356 eq19565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19565 eq71356
  have eq74302 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op y (M.op y (M.op X1 X0))))) = (M.op x (M.op y (M.op x (M.op x (M.op y (M.op y (M.op x (M.op y (M.op y (M.op y (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op y X0))))))))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq13620 eq72904
    | exact resolve eq72904 eq13620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13620 eq72904
  have eq74331 : (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) = (σ (M.op x (M.op y (M.op y (M.op y (M.op y x)))))) := by
    first
    | (have i₁ := eq72952
       have i₂ := eq14502 y (M.op y (M.op y x))
       grind)
    | exact superpose eq14502 eq72952
    | exact resolve eq72952 eq14502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72952
  have eq74847 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op x (M.op y (M.op x (M.op y (M.op y (M.op x (M.op x (M.op y (M.op (σ x) (M.op y (M.op y X0))))))))))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq73468 X0
       have i₂ := eq1263 y y x (M.op y (M.op y (M.op x (M.op x (M.op y (M.op sF2 (M.op y (M.op y X0))))))))
       grind)
    | exact superpose eq1263 eq73468
    | exact resolve eq73468 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73468
  have eq74914 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X1 (M.op X1 X0)))) = (M.op x (M.op y (M.op x (M.op y (M.op y (M.op x (M.op x (M.op y (M.op (τ (M.op X1 X0)) (M.op y (M.op y (τ (M.op X1 X0))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq73535 X0 X1
       have i₂ := eq1263 y y x (M.op y (M.op y (M.op x (M.op x (M.op y (M.op (τ (M.op X1 X0)) (M.op y (M.op y (τ (M.op X1 X0))))))))))
       grind)
    | exact superpose eq1263 eq73535
    | exact resolve eq73535 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73535
  have eq75622 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op x y) (M.op y (M.op X0 (M.op y (M.op x (M.op y (M.op y (M.op x (M.op x (M.op y (M.op X2 (M.op y (M.op y X3))))))))))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq74243 X0 X2 X3
       have i₂ := eq1263 y y x (M.op y (M.op y (M.op x (M.op x (M.op y (M.op X2 (M.op y (M.op y X3))))))))
       grind)
    | exact superpose eq1263 eq74243
    | exact resolve eq74243 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74243
  have eq75625 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 (M.op X2 X3)))) = (M.op (M.op x y) (M.op y (M.op X0 (M.op y (M.op x (M.op y (M.op y (M.op x (M.op x (M.op y (M.op X1 (M.op y (M.op y X3))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq74246 X0 X1 X2 X3
       have i₂ := eq1263 y y x (M.op y (M.op y (M.op x (M.op x (M.op y (M.op X1 (M.op y (M.op y X3))))))))
       grind)
    | exact superpose eq1263 eq74246
    | exact resolve eq74246 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74246
  have eq75666 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op x (M.op x (M.op y (M.op y (M.op x (M.op x (M.op y X0)))))))) := by
    intro X0
    first
    | (have i₁ := eq74287 X0
       have i₂ := eq1263 y y x (M.op y (M.op y (M.op x (M.op x (M.op y X0)))))
       grind)
    | exact superpose eq1263 eq74287
    | exact resolve eq74287 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74287
  have eq75680 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op y (M.op y (M.op X1 X0))))) = (M.op x (M.op y (M.op x (M.op y (M.op y (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op y X0))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq74302 X0 X1
       have i₂ := eq1263 y y x (M.op y (M.op y (M.op y (M.op y (M.op sF0 (M.op y (M.op y (M.op y X0))))))))
       grind)
    | exact superpose eq1263 eq74302
    | exact resolve eq74302 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74302
  have eq76214 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op x (M.op y (M.op x (M.op x (M.op y (M.op x (M.op y (M.op y (M.op (σ x) (M.op y (M.op y X0))))))))))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq74847 X0
       have i₂ := eq14509 (M.op y (M.op sF2 (M.op y (M.op y X0)))) y
       grind)
    | exact superpose eq14509 eq74847
    | exact resolve eq74847 eq14509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74847
  have eq76280 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X1 (M.op X1 X0)))) = (M.op x (M.op y (M.op x (M.op x (M.op y (M.op x (M.op y (M.op y (M.op (τ (M.op X1 X0)) (M.op y (M.op y (τ (M.op X1 X0))))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq74914 X0 X1
       have i₂ := eq14509 (M.op y (M.op (τ (M.op X1 X0)) (M.op y (M.op y (τ (M.op X1 X0)))))) y
       grind)
    | exact superpose eq14509 eq74914
    | exact resolve eq74914 eq14509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74914
  have eq76986 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op (M.op x y) (M.op y (M.op X0 (M.op y (M.op x (M.op x (M.op y (M.op x (M.op y (M.op y (M.op X2 (M.op y (M.op y X3))))))))))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq75622 X0 X2 X3
       have i₂ := eq14509 (M.op y (M.op X2 (M.op y (M.op y X3)))) y
       grind)
    | exact superpose eq14509 eq75622
    | exact resolve eq75622 eq14509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75622
  have eq76989 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 (M.op X2 X3)))) = (M.op (M.op x y) (M.op y (M.op X0 (M.op y (M.op x (M.op x (M.op y (M.op x (M.op y (M.op y (M.op X1 (M.op y (M.op y X3))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq75625 X0 X1 X2 X3
       have i₂ := eq14509 (M.op y (M.op X1 (M.op y (M.op y X3)))) y
       grind)
    | exact superpose eq14509 eq75625
    | exact resolve eq75625 eq14509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75625
  have eq77027 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op x (M.op x (M.op x (M.op y (M.op x (M.op y (M.op y X0)))))))) := by
    intro X0
    first
    | (have i₁ := eq75666 X0
       have i₂ := eq14509 (M.op y X0) y
       grind)
    | exact superpose eq14509 eq75666
    | exact resolve eq75666 eq14509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14509 eq75666
  have eq77040 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op y (M.op y (M.op X1 X0))))) = (M.op x (M.op x (M.op x (M.op y (M.op x (M.op y (M.op y (M.op (M.op x y) (M.op y (M.op y (M.op y X0))))))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq75680 X0 X1
       have i₂ := eq20504 (M.op y (M.op sF0 (M.op y (M.op y (M.op y X0)))))
       grind)
    | exact superpose eq20504 eq75680
    | exact resolve eq75680 eq20504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20504 eq75680
  have eq77539 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op y (M.op y (M.op (σ x) (M.op y (M.op y X0))))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq76214 X0
       have i₂ := eq1263 x y x (M.op y (M.op y (M.op sF2 (M.op y (M.op y X0)))))
       grind)
    | exact superpose eq1263 eq76214
    | exact resolve eq76214 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76214
  have eq77599 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X1 (M.op X1 X0)))) = (M.op y (M.op y (M.op (τ (M.op X1 X0)) (M.op y (M.op y (τ (M.op X1 X0))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq76280 X0 X1
       have i₂ := eq1263 x y x (M.op y (M.op y (M.op (τ (M.op X1 X0)) (M.op y (M.op y (τ (M.op X1 X0)))))))
       grind)
    | exact superpose eq1263 eq76280
    | exact resolve eq76280 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76280
  have eq78312 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X1 (M.op y (M.op y (M.op X1 X0))))) = (M.op x (M.op x (M.op x (M.op x (M.op x (M.op y (M.op y (M.op y X0)))))))) := by
    intro X0 X1
    first
    | exact superpose eq14428 eq77040
    | exact resolve eq77040 eq14428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77040
  have eq190797 : ∀ X0 : G, (M.op (σ x) X0) ≠ (M.op (σ x) (M.op (σ y) (σ x))) ∨ (M.op (σ x) X0) = (k X0 (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq49697 eq186
    | (have j0 := eq186 X0
       grind)
    | (have r₁ := eq186 (M.op (σ y) (σ x))
       have r₂ := eq49697 (σ x) (σ y)
       grind)
    | exact resolve eq186 eq49697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326386 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op y (M.op y (M.op (σ x) (M.op y (M.op y (M.op X0 (M.op (σ x) (σ y)))))))))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f326386_14 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op X1 (M.op (σ x) (M.op X0 (M.op X1 (M.op (σ x) (σ y))))))) := by
      intro X0 X1
      grind
    have f326386_15 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op y (M.op y (M.op (σ x) (M.op y (M.op y X0))))) ∨ (σ y) = (σ x) ∨ x = (M.op x y) := by
      intro X0
      grind
    have f326386_24 : (σ y) ≠ (M.op (σ y) (M.op X0 (M.op y (M.op y (M.op (σ x) (M.op y (M.op y (M.op X0 (M.op (σ x) (σ y)))))))))) := by grind
    have f326386_25 : (σ y) ≠ (σ x) := by grind
    have f326386_26 : x ≠ (M.op x y) := by grind
    have f326386_27 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op y (M.op y (M.op (σ x) (M.op y (M.op y X0))))) ∨ x = (M.op x y) := by
      intro X0
      first
      | (have j0 := f326386_15 X0
         grind)
      | (have r₁ := f326386_15 X0
         have r₂ := f326386_25
         grind)
      | exact resolve f326386_15 f326386_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f326386_28 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op y (M.op y (M.op (σ x) (M.op y (M.op y X0))))) := by
      intro X0
      first
      | (have j0 := f326386_27 X0
         grind)
      | (have r₁ := f326386_27 X0
         have r₂ := f326386_26
         grind)
      | exact resolve f326386_27 f326386_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f326386_174 : (σ y) ≠ (M.op (σ y) (M.op X0 (M.op (σ x) (M.op (σ y) (M.op X0 (M.op (σ x) (σ y))))))) := by
      first
      | (have i₁ := f326386_24
         have i₂ := f326386_28 (M.op X0 (M.op (σ x) (σ y)))
         grind)
      | exact superpose f326386_28 f326386_24
      | exact resolve f326386_24 f326386_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f326386_175 : False := by
      first
      | (have r₁ := f326386_174
         have r₂ := f326386_14 (σ y) X0
         grind)
      | exact resolve f326386_174 f326386_14
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f326386_175
  have eq326396 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (M.op y (M.op y (M.op (σ x) (M.op y (M.op y (M.op (σ x) (σ y)))))))))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq77539 eq12573
    | exact resolve eq12573 eq77539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12573 eq77539
  have eq326397 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq326396
       have i₂ := eq1263 y y sF2 sF4
       grind)
    | exact superpose eq1263 eq326396
    | exact resolve eq326396 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326396
  have eq326408 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) X0) ∨ (M.op (σ x) X0) = (k X0 (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq326397 eq186
    | (have j0 := eq186 X0
       grind)
    | exact resolve eq186 eq326397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq326419 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq326397 eq49697
    | exact resolve eq49697 eq326397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq326421 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (M.op (σ y) (M.op X0 (σ y))))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq326397 eq1263
    | exact resolve eq1263 eq326397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326397
  have eq326430 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq326419
  have eq326447 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13180 eq326421
    | (have j0 := eq326421 (σ x)
       grind)
    | exact resolve eq326421 eq13180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13180 eq326421
  have eq326512 : (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ y) (σ x)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43449 eq326447
    | exact resolve eq326447 eq43449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326447
  have eq326539 : (σ x) = (M.op (σ x) (M.op (σ x) (M.op (σ y) (σ x)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq326512
  have eq326649 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ y) (σ x))) = (M.op X0 (M.op X1 (M.op (σ x) (M.op X0 (M.op X1 (σ x)))))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq326539 eq1263
    | exact resolve eq1263 eq326539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326539
  have eq335145 : (σ y) ≠ (σ y) ∨ (σ y) = (k (M.op (σ y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq326430 eq326408
    | (have r₁ := eq326408 (M.op (σ y) (σ x))
       have r₂ := eq326430
       grind)
    | exact resolve eq326408 eq326430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326408 eq326430
  have eq335162 : (σ y) ≠ (σ y) ∨ (σ y) = (k (M.op (σ y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq335145
  have eq335163 : (σ y) = (k (M.op (σ y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq335162
  have eq335195 : (τ (σ y)) = (k (τ (M.op (σ y) (σ x))) (τ (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq335163 eq398
    | exact resolve eq398 eq335163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335163
  have eq335221 : y = (k (τ (M.op (σ y) (σ x))) (τ (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39 eq335195
    | exact resolve eq335195 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq335195
  have eq752017 : (M.op (σ x) (M.op (σ y) (σ x))) = (k (M.op (σ y) (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq190797 (M.op (σ y) (σ x))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190797
  have eq752055 : (τ (M.op (σ x) (M.op (σ y) (σ x)))) = (k (τ (M.op (σ y) (σ x))) (τ (M.op (σ y) (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq752017 eq398
    | exact resolve eq398 eq752017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398 eq752017
  have eq752136 : y = (τ (M.op (σ x) (M.op (σ y) (σ x)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq752055 eq335221
    | exact resolve eq335221 eq752055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335221 eq752055
  have eq752160 : y = (τ (M.op (σ x) (M.op (σ y) (σ x)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq752136
  have eq752177 : ∀ X0 X1 : G, y = (τ (M.op X0 (M.op X1 (M.op (σ x) (M.op X0 (M.op X1 (σ x))))))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq326649 eq752160
    | exact resolve eq752160 eq326649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326649 eq752160
  have eq752309 : ∀ X0 X1 : G, y = (τ (M.op X0 (M.op X1 (M.op (σ x) (M.op X0 (M.op X1 (σ x))))))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq752177 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752177
  have eq896859 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq326386 sF2
       have i₂ := eq1263 y y sF2 (M.op sF2 sF4)
       grind)
    | exact superpose eq1263 eq326386
    | exact resolve eq326386 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq326386
  have eq896873 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq896859 eq49697
    | exact resolve eq49697 eq896859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49697 eq896859
  have eq896881 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq896873
  have eq896970 : y = (τ (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq896881 eq752309
    | exact resolve eq752309 eq896881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752309 eq896881
  have eq896977 : y = (τ (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y))))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq896970
  have eq896997 : y = (M.op y (M.op y (M.op (τ (M.op (σ x) (σ y))) (M.op y (M.op y (τ (M.op (σ x) (σ y)))))))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq896977
       have i₂ := eq77599 sF3 sF2
       grind)
    | exact superpose eq77599 eq896977
    | exact resolve eq896977 eq77599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77599 eq896977
  have eq897007 : y = (M.op y (M.op y (M.op (τ (M.op (σ x) (σ y))) (M.op y (M.op y (τ (M.op (σ x) (σ y)))))))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq896997
    | exact resolve eq896997 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq896997
  have eq915238 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq897007 eq1263
    | exact resolve eq1263 eq897007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897007
  have eq915244 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq43449 eq915238
    | exact resolve eq915238 eq43449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43449 eq915238
  have eq915269 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq915244
  have eq915273 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq915269
    | exact resolve eq915269 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq915269
  have eq915276 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq915273
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq915273
    | exact resolve eq915273 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915273
  have eq915277 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq915276
  have eq915278 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq915277 eq26
    | exact resolve eq26 eq915277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq915285 : (k (σ x) (σ x)) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq915277 eq66
    | exact resolve eq66 eq915277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq915277
  have eq916970 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq915285
       have i₂ := eq127 sF2
       grind)
    | exact superpose eq127 eq915285
    | exact resolve eq915285 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq915285
  have eq923100 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24823 x y
       have i₂ := eq916970
       grind)
    | exact superpose eq916970 eq24823
    | (have j0 := eq24823 x y
       grind)
    | exact resolve eq24823 eq916970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24823 eq916970
  have eq923946 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq923100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq923100
    | exact resolve eq923100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923100
  have eq923962 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq923946
    | exact resolve eq923946 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923946
  have eq923969 : x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq923962
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq923962
    | exact resolve eq923962 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923962
  have eq923970 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (M.op y x) = (M.op y y) := by grind
  clear eq923969
  have eq1011641 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (M.op y x) = (M.op y y) := by
    first
    | exact superpose eq923970 eq915278
    | exact resolve eq915278 eq923970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923970
  have eq1011645 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op y x) = (M.op y y) := by grind
  clear eq1011641
  have eq1011648 : (M.op y x) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1011645
       have r₂ := eq27
       grind)
    | exact resolve eq1011645 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011645
  have eq1011701 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op y (M.op y x)))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12575 y y
       have i₂ := eq1011648
       grind)
    | exact superpose eq1011648 eq12575
    | exact resolve eq12575 eq1011648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011648
  have eq1011729 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq12575 eq1011701
    | exact resolve eq1011701 eq12575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011701
  have eq1011735 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1011729
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1011729
    | exact resolve eq1011729 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1011729
  have eq1011764 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq138 x
       have i₂ := eq1011735
       grind)
    | exact superpose eq1011735 eq138
    | exact resolve eq138 eq1011735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011735
  have eq1011789 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1011764
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1011764
    | exact resolve eq1011764 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011764
  have eq1011793 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1011789
    | exact resolve eq1011789 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011789
  have eq1011829 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1011793 eq915278
    | exact resolve eq915278 eq1011793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915278 eq1011793
  have eq1011877 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1011829
  have eq1011904 : x = (M.op x y) := by
    first
    | (have r₁ := eq1011877
       have r₂ := eq27
       grind)
    | exact resolve eq1011877 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011877
  have eq1011917 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1011904 eq20
    | exact resolve eq20 eq1011904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1011925 : ∀ X0 : G, (M.op x (M.op y (M.op x X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1011904 eq52
    | exact resolve eq52 eq1011904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1011926 : y = (M.op x (M.op y x)) := by
    first
    | exact superpose eq1011904 eq79
    | exact resolve eq79 eq1011904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq1012454 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op x (M.op y (M.op X1 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq1011904 eq12575
    | exact resolve eq12575 eq1011904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12575
  have eq1012456 : ∀ X0 X1 : G, (M.op x X0) = (M.op X1 (M.op y (M.op x (M.op X1 X0)))) := by
    intro X0 X1
    first
    | exact superpose eq1011904 eq12596
    | exact resolve eq12596 eq1011904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12596
  have eq1012471 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 (M.op X3 (M.op X1 (M.op X2 (M.op x X0)))))) = (M.op x (M.op y (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1011904 eq13625
    | exact resolve eq13625 eq1011904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13625
  have eq1012522 : ∀ X0 X1 X2 : G, (M.op X2 (M.op y X0)) = (M.op x (M.op X1 (M.op x (M.op X2 (M.op X1 X0))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1011904 eq14378
    | exact resolve eq14378 eq1011904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14378
  have eq1012538 : ∀ X0 X1 X2 : G, (M.op x (M.op X2 X0)) = (M.op X1 (M.op X2 (M.op y (M.op X1 (M.op x X0))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq1011904 eq14428
    | exact resolve eq14428 eq1011904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14428
  have eq1012982 : ∀ X0 X1 : G, (M.op x (M.op y (M.op x X0))) = (M.op X1 (M.op y (M.op x (M.op X1 (M.op x (M.op y X0)))))) := by
    intro X0 X1
    first
    | exact superpose eq1011904 eq19568
    | exact resolve eq19568 eq1011904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19568
  have eq1013004 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y (M.op x (M.op x (M.op y (M.op y X0))))) := by
    intro X0
    first
    | exact superpose eq1011904 eq20427
    | exact resolve eq20427 eq1011904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20427
  have eq1013865 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op x (M.op y (M.op x (M.op x (M.op y (M.op y (M.op X1 (M.op y (M.op x (M.op x (M.op y X0))))))))))) := by
    intro X0 X1
    first
    | exact superpose eq1011904 eq71307
    | exact resolve eq71307 eq1011904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71307
  have eq1013868 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (σ (M.op x (M.op y (M.op y (M.op y (M.op y x)))))) := by
    first
    | exact superpose eq1011904 eq74331
    | exact resolve eq74331 eq1011904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74331
  have eq1013921 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op x (M.op y (M.op X0 (M.op y (M.op x (M.op x (M.op y (M.op x (M.op y (M.op y (M.op X2 (M.op y (M.op y X3))))))))))))) := by
    intro X0 X2 X3
    first
    | exact superpose eq1011904 eq76986
    | exact resolve eq76986 eq1011904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76986
  have eq1013924 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 (M.op X2 X3)))) = (M.op x (M.op y (M.op X0 (M.op y (M.op x (M.op x (M.op y (M.op x (M.op y (M.op y (M.op X1 (M.op y (M.op y X3))))))))))))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1011904 eq76989
    | exact resolve eq76989 eq1011904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76989
  have eq1013937 : ∀ X0 X1 : G, (M.op x (M.op x (M.op x (M.op x (M.op x (M.op y (M.op y (M.op y X0)))))))) = (M.op x (M.op X1 (M.op y (M.op y (M.op X1 X0))))) := by
    intro X0 X1
    first
    | exact superpose eq1011904 eq78312
    | exact resolve eq78312 eq1011904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78312 eq1011904
  have eq1017922 : (M.op (σ (M.op x x)) (σ (M.op x x))) = (σ (M.op x (M.op x (M.op x (M.op x (M.op x (M.op y (M.op y (M.op y x))))))))) := by
    first
    | (have i₁ := eq1013868
       have i₂ := eq1013937 x y
       grind)
    | exact superpose eq1013937 eq1013868
    | exact resolve eq1013868 eq1013937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013868 eq1013937
  have eq1018265 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op x (M.op x (M.op x (M.op X1 (M.op y (M.op x (M.op x (M.op y X0)))))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1013865 X0 X1
       have i₂ := eq1013004 (M.op X1 (M.op y (M.op x (M.op x (M.op y X0)))))
       grind)
    | exact superpose eq1013004 eq1013865
    | exact resolve eq1013865 eq1013004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013865
  have eq1018527 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op x (M.op x (M.op y (M.op y X0))))) := by
    intro X0
    first
    | (have i₁ := eq77027 X0
       have i₂ := eq1012522 X0 y y
       grind)
    | exact superpose eq1012522 eq77027
    | exact resolve eq77027 eq1012522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77027
  have eq1018550 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op x (M.op y (M.op X0 (M.op y (M.op x (M.op y (M.op y (M.op X2 (M.op y (M.op y X3)))))))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1013921 X0 X2 X3
       have i₂ := eq1012522 (M.op X2 (M.op y (M.op y X3))) y y
       grind)
    | exact superpose eq1012522 eq1013921
    | exact resolve eq1013921 eq1012522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013921
  have eq1018553 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 (M.op X2 X3)))) = (M.op x (M.op y (M.op X0 (M.op y (M.op x (M.op y (M.op y (M.op X1 (M.op y (M.op y X3)))))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1013924 X0 X1 X2 X3
       have i₂ := eq1012522 (M.op X1 (M.op y (M.op y X3))) y y
       grind)
    | exact superpose eq1012522 eq1013924
    | exact resolve eq1013924 eq1012522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013924
  have eq1019034 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op x (M.op x (M.op y (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14502 X0 X1
       have i₂ := eq1012471 X1 x y X0
       grind)
    | exact superpose eq1012471 eq14502
    | exact resolve eq14502 eq1012471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14502 eq1012471
  have eq1019069 : ∀ X0 : G, (M.op x (M.op y (M.op x X0))) = (M.op x (M.op x (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq1012982 X0 x
       have i₂ := eq1012456 (M.op x (M.op y X0)) x
       grind)
    | exact superpose eq1012456 eq1012982
    | exact resolve eq1012982 eq1012456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012456 eq1012982
  have eq1019602 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1011917
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1011917
    | exact resolve eq1011917 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011917
  have eq1020095 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op x (M.op x (M.op x (M.op x (M.op x (M.op y (M.op y (M.op y x))))))))) := by
    first
    | (have i₁ := eq1017922
       have i₂ := eq138 x
       grind)
    | exact superpose eq138 eq1017922
    | exact resolve eq1017922 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138 eq1017922
  have eq1020305 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op x (M.op x (M.op x (M.op X1 (M.op y X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1018265 X0 X1
       have i₂ := eq1012538 (M.op y X0) x X1
       grind)
    | exact superpose eq1012538 eq1018265
    | exact resolve eq1018265 eq1012538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012538 eq1018265
  have eq1020678 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 (M.op X2 X3)))) = (M.op x (M.op y (M.op X0 (M.op x (M.op X1 (M.op y (M.op y X3))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1018553 X0 X1 X2 X3
       have i₂ := eq1012454 (M.op X1 (M.op y (M.op y X3))) y
       grind)
    | exact superpose eq1012454 eq1018553
    | exact resolve eq1018553 eq1012454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018553
  have eq1020681 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op x (M.op y (M.op X0 (M.op x (M.op X2 (M.op y (M.op y X3))))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1018550 X0 X2 X3
       have i₂ := eq1012454 (M.op X2 (M.op y (M.op y X3))) y
       grind)
    | exact superpose eq1012454 eq1018550
    | exact resolve eq1018550 eq1012454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012454 eq1018550
  have eq1020966 : ∀ X0 : G, (M.op x (M.op x X0)) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq1013004 X0
       have i₂ := eq1019034 y X0
       grind)
    | exact superpose eq1019034 eq1013004
    | exact resolve eq1013004 eq1019034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013004
  have eq1020967 : ∀ X0 : G, (M.op y (M.op x X0)) = (M.op x (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq1018527 X0
       have i₂ := eq1019034 y X0
       grind)
    | exact superpose eq1019034 eq1018527
    | exact resolve eq1018527 eq1019034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018527
  have eq1021032 : ∀ X0 : G, (M.op x (M.op x (M.op y X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1019069 X0
       have i₂ := eq1011925 X0
       grind)
    | exact superpose eq1011925 eq1019069
    | exact resolve eq1019069 eq1011925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011925 eq1019069
  have eq1021080 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1019602 eq22
    | exact resolve eq22 eq1019602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq1021081 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1019602 eq26
    | exact resolve eq26 eq1019602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1019602
  have eq1023764 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op x (M.op x (M.op x (M.op y (M.op y x)))))) := by
    first
    | (have i₁ := eq1020095
       have i₂ := eq1019034 y (M.op y x)
       grind)
    | exact superpose eq1019034 eq1020095
    | exact resolve eq1020095 eq1019034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019034 eq1020095
  have eq1024646 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 (M.op X0 (M.op X2 X3)))) = (M.op x (M.op y (M.op X0 (M.op x (M.op X1 (M.op x (M.op x X3))))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1020678 X0 X1 X2 X3
       have i₂ := eq1020966 X3
       grind)
    | exact superpose eq1020966 eq1020678
    | exact resolve eq1020678 eq1020966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020678
  have eq1024649 : ∀ X0 X2 X3 : G, (M.op (M.op X0 X2) X3) = (M.op x (M.op y (M.op X0 (M.op x (M.op X2 (M.op x (M.op x X3))))))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq1020681 X0 X2 X3
       have i₂ := eq1020966 X3
       grind)
    | exact superpose eq1020966 eq1020681
    | exact resolve eq1020681 eq1020966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020681 eq1020966
  have eq1025960 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op y (M.op x x))) := by
    first
    | (have i₁ := eq1023764
       have i₂ := eq1020305 x y
       grind)
    | exact superpose eq1020305 eq1023764
    | exact resolve eq1023764 eq1020305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020305 eq1023764
  have eq1028025 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op x (M.op y x))) := by
    first
    | (have i₁ := eq1025960
       have i₂ := eq1020967 x
       grind)
    | exact superpose eq1020967 eq1025960
    | exact resolve eq1025960 eq1020967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020967 eq1025960
  have eq1029403 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq1028025
       have i₂ := eq1011926
       grind)
    | exact superpose eq1011926 eq1028025
    | exact resolve eq1028025 eq1011926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011926 eq1028025
  have eq1030594 : (σ y) = (M.op x (M.op y (M.op (σ x) (M.op x (M.op (σ x) (M.op x (M.op x (M.op (σ x) (σ x))))))))) := by
    first
    | (have i₁ := eq1029403
       have i₂ := eq1024649 (σ x) (σ x) (M.op (σ x) (σ x))
       grind)
    | exact superpose eq1024649 eq1029403
    | exact resolve eq1029403 eq1024649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024649 eq1029403
  have eq1031701 : (σ y) = (M.op x (M.op y (M.op (σ x) (M.op x (M.op y (σ x)))))) := by
    first
    | (have i₁ := eq1030594
       have i₂ := eq1012522 (σ x) (σ x) x
       grind)
    | exact superpose eq1012522 eq1030594
    | exact resolve eq1030594 eq1012522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012522 eq1030594
  have eq1032729 : (σ y) = (M.op x (M.op x (M.op y (M.op x (M.op x (M.op (σ x) (M.op x (M.op x (σ x))))))))) := by
    first
    | (have i₁ := eq1031701
       have i₂ := eq1024646 x (σ x) y (σ x)
       grind)
    | exact superpose eq1024646 eq1031701
    | exact resolve eq1031701 eq1024646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024646 eq1031701
  have eq1033637 : (σ y) = (M.op x (M.op x (M.op (σ x) (M.op x (M.op x (σ x)))))) := by
    first
    | (have i₁ := eq1032729
       have i₂ := eq1021032 (M.op x (M.op x (M.op (σ x) (M.op x (M.op x (σ x))))))
       grind)
    | exact superpose eq1021032 eq1032729
    | exact resolve eq1032729 eq1021032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021032 eq1032729
  have eq1034497 : (σ y) = (M.op x (M.op x (M.op (σ (M.op x y)) (M.op x (M.op x (σ (M.op x y))))))) := by
    first
    | (have i₁ := eq1033637
       have i₂ := eq1021080
       grind)
    | exact superpose eq1021080 eq1033637
    | exact resolve eq1033637 eq1021080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021080 eq1033637
  have eq1035728 : (σ y) = (M.op x (M.op x (M.op (σ (M.op x y)) (M.op x (M.op x (σ (M.op x y))))))) := by
    first
    | (have i₁ := eq1034497
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1034497
    | exact resolve eq1034497 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1034497
  have eq1054657 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1035728 eq1263
    | exact resolve eq1263 eq1035728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263 eq1035728
  have eq1054670 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1021081 eq1054657
    | exact resolve eq1054657 eq1021081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021081 eq1054657
  have eq1054711 : False := by grind
  exact eq1054711

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,Y) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxy_pyy_pyx_x_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq59
    | (have j0 := eq59 (σ X0) (σ X1)
       grind)
    | exact resolve eq59 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq18
    | exact resolve eq18 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq86 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq85
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq94 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq86
    | exact resolve eq86 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq86
  have eq98 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq94 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq94
    | exact resolve eq94 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq182 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq70 y x
       grind)
    | exact superpose eq70 eq16
    | (have j1 := eq70 y x
       grind)
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq201 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (M.op (σ X0) X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq9
    | exact resolve eq9 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq752 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq182
       have i₂ := eq98 x
       grind)
    | exact superpose eq98 eq182
    | exact resolve eq182 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq753 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq752
       have i₂ := eq59 y x
       grind)
    | exact superpose eq59 eq752
    | (have j1 := eq59 y x
       grind)
    | exact resolve eq752 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq752
  have eq754 : (M.op x x) = (M.op y x) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by grind
  clear eq753
  have eq4592 : ∀ X0 : G, y = (M.op (M.op x x) (M.op (M.op x X0) X0)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq754
       grind)
    | exact superpose eq754 eq9
    | exact resolve eq9 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq4619 : x = y ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq4592 x
       have i₂ := eq9 x x x
       grind)
    | exact superpose eq9 eq4592
    | exact resolve eq4592 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4592
  have eq4626 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4619
       grind)
    | exact superpose eq4619 eq16
    | exact resolve eq16 eq4619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4619
  have eq4627 : (M.op (σ y) (σ x)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq4626
       have r₂ := eq98 x
       grind)
    | exact resolve eq4626 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4626
  have eq4779 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x x)) (M.op (M.op (σ x) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) (σ x) X0
       have i₂ := eq4627
       grind)
    | exact superpose eq4627 eq9
    | exact resolve eq9 eq4627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4627
  have eq4803 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4779 x
       have i₂ := eq201 x x
       grind)
    | exact superpose eq201 eq4779
    | exact resolve eq4779 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201 eq4779
  have eq5021 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4803
       grind)
    | exact superpose eq4803 eq10
    | exact resolve eq10 eq4803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4803
  have eq5068 : x = y := by
    first
    | (have i₁ := eq5021
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq5021
    | exact resolve eq5021 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5021
  have eq5070 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5068
       grind)
    | exact superpose eq5068 eq16
    | exact resolve eq16 eq5068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5068
  have eq5073 : False := by grind
  exact eq5073

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyx_pyy_pyx_pyy_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
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
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq65 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq65 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq65 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq65 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq72 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq67 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq67 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq67 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq127 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq68 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq68
    | (have j0 := eq68 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq68 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq68 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq68 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq138 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq127 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq142 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq138 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq138 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq138 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq138 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq143 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq142 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq142
    | (have j0 := eq142 X0 X1
       grind)
    | exact resolve eq142 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq142
  have eq169 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq72 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq173 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq169 X0 X1
       have j1 := eq143 X1 X0
       grind)
    | (have r₁ := eq169 X1 X1
       have r₂ := eq143 X1 X1
       grind)
    | (have r₁ := eq169 X1 X0
       have r₂ := eq143 X0 X1
       grind)
    | exact resolve eq169 eq143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq169
  have eq728 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq173 (σ X1) (σ X0)
       grind)
    | exact superpose eq173 eq15
    | exact resolve eq15 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq731 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq728 X0 X1
       have i₂ := eq173 X1 X0
       grind)
    | exact superpose eq173 eq728
    | exact resolve eq728 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173 eq728
  have eq735 : False := by grind
  exact eq735

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,Y) else if m(X,X) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxx_pyx_pyy_pxy_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op y X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq67 sF2
       grind)
    | exact superpose eq67 eq49
    | exact resolve eq49 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq71
       have i₂ := eq67 x
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq71
  have eq101 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq101
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq101
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq110
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq110
    | exact resolve eq110 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq118 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq39482 : ∀ X0 : G, y = (M.op (M.op x x) (M.op (M.op x X0) X0)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq118
       grind)
    | exact superpose eq118 eq14
    | exact resolve eq14 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq39541 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq39482 x
       have i₂ := eq14 x x x
       grind)
    | exact superpose eq14 eq39482
    | exact resolve eq39482 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39482
  have eq39583 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq39541 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq39541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39541
  have eq39592 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq39583
    | exact resolve eq39583 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39583
  have eq39603 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq39592
       have r₂ := eq27
       grind)
    | exact resolve eq39592 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39592
  have eq39607 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq39603
    | exact resolve eq39603 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39603
  have eq39622 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (M.op (σ x) X0) X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq39607 eq14
    | exact resolve eq14 eq39607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39607
  have eq39681 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq39622 x
       have i₂ := eq14 sF2 sF2 x
       grind)
    | exact superpose eq14 eq39622
    | exact resolve eq39622 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39622
  have eq39746 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq39681 eq14
    | exact resolve eq14 eq39681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39681
  have eq39779 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq51 eq39746
    | exact resolve eq39746 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq39746
  have eq39780 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq39779
  have eq40447 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq39780
       grind)
    | exact superpose eq39780 eq14
    | exact resolve eq14 eq39780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39780
  have eq40480 : x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq50 eq40447
    | exact resolve eq40447 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq40447
  have eq40481 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq40480
  have eq40505 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq40481 eq29
    | exact resolve eq29 eq40481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq40481
  have eq40656 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq40505
    | exact resolve eq40505 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq40505
  have eq40657 : x = y := by grind
  clear eq40656
  have eq40679 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq40657
       grind)
    | exact superpose eq40657 eq18
    | exact resolve eq18 eq40657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq40680 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq40657
       grind)
    | exact superpose eq40657 eq24
    | exact resolve eq24 eq40657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq40657
  have eq40839 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq40680
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq40680
    | exact resolve eq40680 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq40680
  have eq40874 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq40839 eq26
    | exact resolve eq26 eq40839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq40839
  have eq41180 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq40874 eq72
    | exact resolve eq72 eq40874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq40874
  have eq41266 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq41180
       have i₂ := eq40679
       grind)
    | exact superpose eq40679 eq41180
    | exact resolve eq41180 eq40679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40679 eq41180
  have eq41281 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq41266 eq15
    | exact resolve eq15 eq41266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41266
  have eq41371 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq41281
    | exact resolve eq41281 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq41281
  have eq41392 : False := by grind
  exact eq41392

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pyy_pyy_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op X1 X2) X2) X3) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) (M.op (M.op X1 X2) X2) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 (M.op (M.op X2 X3) X3))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 (M.op X0 X2) (M.op (M.op X2 X3) X3)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
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
  have eq38 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq36 (σ X0)
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq38
    | exact resolve eq38 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq38
  have eq60 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq65 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq60
    | (have j0 := eq60 X0 X1
       grind)
    | exact resolve eq60 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq89 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (M.op (σ X0) X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq9
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X2) X2) x
       have i₂ := eq20 (M.op X0 (M.op (M.op X1 X2) X2)) X1 X2 x
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq158 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 (σ X0))) (M.op X2 (M.op (σ (M.op X0 X0)) (σ X0)))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X2 X1 (σ X0) (σ X0)
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq21
    | exact resolve eq21 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq332 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
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
  clear eq65
  have eq3318 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op (M.op (σ X2) X3) X3)) (M.op (σ (M.op X2 X2)) (σ X2)))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq158 X2 X1 (M.op X0 (M.op (M.op (σ X2) X3) X3))
       have i₂ := eq105 X0 (σ X2) X3
       grind)
    | exact superpose eq105 eq158
    | exact resolve eq158 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq158
  have eq3526 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq332
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq332
    | (have j1 := eq14 (σ (M.op x x)) (M.op (σ y) (σ x))
       grind)
    | (have r₁ := eq332
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq332
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq332 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq3527 : x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (M.op x x) = (M.op y x) := by grind
  clear eq3526
  have eq30041 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3527
       grind)
    | exact superpose eq3527 eq16
    | exact resolve eq16 eq3527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3527
  have eq30042 : (M.op x x) = (M.op y x) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq30041
       have r₂ := eq43 x
       grind)
    | exact resolve eq30041 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30041
  have eq61375 : ∀ X0 X1 : G, y = (M.op (M.op x x) (M.op (M.op x (M.op (M.op (σ X0) X1) X1)) (M.op (σ (M.op X0 X0)) (σ X0)))) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq3318 x y X0 X1
       have i₂ := eq30042
       grind)
    | exact superpose eq30042 eq3318
    | exact resolve eq3318 eq30042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30042
  have eq61381 : x = y ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq61375 x x
       have i₂ := eq3318 x x x x
       grind)
    | exact superpose eq3318 eq61375
    | exact resolve eq61375 eq3318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3318 eq61375
  have eq61659 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq61381
       grind)
    | exact superpose eq61381 eq16
    | exact resolve eq16 eq61381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61381
  have eq61660 : (σ x) = (σ y) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq61659
       have r₂ := eq43 x
       grind)
    | exact resolve eq61659 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61659
  have eq61662 : y = (τ (σ x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq61660
       grind)
    | exact superpose eq61660 eq10
    | exact resolve eq10 eq61660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61660
  have eq61764 : x = y ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq61662
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq61662
    | exact resolve eq61662 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61662
  have eq61920 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq61764
       grind)
    | exact superpose eq61764 eq16
    | exact resolve eq16 eq61764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61764
  have eq61921 : (σ (M.op x x)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq61920
       have r₂ := eq43 x
       grind)
    | exact resolve eq61920 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61920
  have eq61957 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x x)) (M.op (M.op (σ x) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) (σ x) X0
       have i₂ := eq61921
       grind)
    | exact superpose eq61921 eq9
    | exact resolve eq9 eq61921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61921
  have eq62045 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq61957 x
       have i₂ := eq89 x x
       grind)
    | exact superpose eq89 eq61957
    | exact resolve eq61957 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq61957
  have eq64136 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq62045
       grind)
    | exact superpose eq62045 eq16
    | exact resolve eq16 eq62045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64137 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq62045
       grind)
    | exact superpose eq62045 eq10
    | exact resolve eq10 eq62045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62045
  have eq64240 : x = y := by
    first
    | (have i₁ := eq64137
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq64137
    | exact resolve eq64137 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64137
  have eq64241 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq64136
       have i₂ := eq43 x
       grind)
    | exact superpose eq43 eq64136
    | exact resolve eq64136 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq64136
  have eq64242 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq64241
       have i₂ := eq64240
       grind)
    | exact superpose eq64240 eq64241
    | exact resolve eq64241 eq64240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64240 eq64241
  have eq64243 : False := by grind
  exact eq64243
