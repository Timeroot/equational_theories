import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4533`: `x ◇ (y ◇ z) = (y ◇ z) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_x_pyx_pxy_Equation4533 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4533 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4533.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X1 X2) X2) := by
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
  have eq177 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op (M.op (M.op X0 X1) X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X0 (M.op X1 X2)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X0 (M.op X1 X2)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X1 X2) X2
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op x y) y) := by
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
  have eq180 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X1 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq16 X3 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ X2 ∨ (M.op X0 X1) = (k (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 X1) X2
       have i₂ := eq16 X2 X0 X1
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 (M.op X0 X1) X2
       grind)
    | (have r₁ := eq13 (M.op X1 X2) (M.op (M.op X1 X2) X2)
       have r₂ := eq16 (M.op (M.op X1 X2) X2) X1 X2
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X1 X2
       have i₂ := eq16 (M.op (M.op X0 X1) X1) X0 X1
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq188 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 : G, (M.op (M.op x y) y) ≠ X0 ∨ (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq179 eq13
    | (have j0 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op (M.op x y) y)
       have r₂ := eq179 (M.op (M.op x y) y)
       grind)
    | exact resolve eq13 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq179 eq188
    | exact resolve eq188 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq195 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X1 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq180 eq180
    | exact resolve eq180 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 : G, (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq180 eq196
    | exact resolve eq196 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq196
  have eq252 : (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) y) := by
    first
    | exact superpose eq193 eq16
    | exact resolve eq16 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq276 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) := by
    first
    | exact superpose eq201 eq16
    | exact resolve eq16 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq528 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq530 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) y) ∨ y = (M.op (M.op (M.op x y) y) y) ∨ y = (M.op y (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq252
       have i₂ := eq11 (M.op sF0 y) y
       grind)
    | exact superpose eq11 eq252
    | (have j1 := eq11 (M.op (M.op x y) y) y
       grind)
    | exact resolve eq252 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq559 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have i₁ := eq276
       have i₂ := eq11 (M.op sF4 sF3) sF3
       grind)
    | exact superpose eq11 eq276
    | (have j1 := eq11 (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)
       grind)
    | exact resolve eq276 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq572 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | (have j1 := eq183 (M.op (σ x) (σ y)) (σ y) (σ y)
       grind)
    | (have r₁ := eq559
       have r₂ := eq183 (σ x) (σ y) (k (M.op (M.op (σ x) (σ y)) (σ y)) (σ y))
       grind)
    | (have r₁ := eq559
       have r₂ := eq183 (M.op (σ x) (σ y)) (σ y) (σ y)
       grind)
    | exact resolve eq559 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq588 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) y) ∨ y = (M.op y (M.op (M.op x y) y)) := by
    first
    | (have j1 := eq183 (M.op x y) y y
       grind)
    | (have r₁ := eq558
       have r₂ := eq183 x y (k (M.op (M.op x y) y) y)
       grind)
    | (have r₁ := eq558
       have r₂ := eq183 (M.op x y) y y
       grind)
    | exact resolve eq558 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq558
  have eq598 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)) := by
    first
    | (have j1 := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)
       grind)
    | (have r₁ := eq587
       have r₂ := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) (σ y)
       grind)
    | exact resolve eq587 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq599 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) y) := by
    first
    | (have j1 := eq13 (M.op (M.op x y) y) y
       grind)
    | (have r₁ := eq588
       have r₂ := eq13 (M.op (M.op x y) y) y
       grind)
    | exact resolve eq588 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq801 : (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (k (τ (M.op (M.op (σ x) (σ y)) (σ y))) y) := by
    first
    | exact superpose eq598 eq152
    | exact resolve eq152 eq598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq598
  have eq1239 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq1271 : (M.op x y) = (k (M.op x y) (M.op (M.op x y) y)) := by
    first
    | (have j0 := eq189 (M.op (M.op x y) y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq1274 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq179 eq1271
    | exact resolve eq1271 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1271
  have eq1289 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq1274 eq37
    | exact resolve eq37 eq1274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq1274
  have eq1290 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq1289
    | (have j0 := eq1289 X0
       grind)
    | exact resolve eq1289 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1289
  have eq1558 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X4 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X3 X4 (M.op X1 X2)
       have i₂ := eq181 (M.op X4 (M.op X1 X2)) X1 X2 X0
       grind)
    | (have i₁ := eq16 X3 X4 (M.op X1 X2)
       have i₂ := eq181 X0 X1 X2 (M.op X4 (M.op X1 X2))
       grind)
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2436 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq528
       grind)
    | exact superpose eq528 eq40
    | exact resolve eq40 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq2437 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2436
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2436
    | exact resolve eq2436 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2436
  have eq2439 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq2437
    | exact resolve eq2437 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2437
  have eq2785 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X3)) ≠ (M.op X0 (M.op X1 (M.op X2 X3))) ∨ (k X3 (M.op X1 (M.op X2 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 (M.op X1 (M.op X2 X3))
       have i₂ := eq178 X1 X2 X3 X0
       grind)
    | exact superpose eq178 eq13
    | (have j0 := eq13 X3 (M.op X1 (M.op X2 X3))
       grind)
    | (have r₁ := eq13 (M.op X0 (M.op X1 X2)) (M.op (M.op X0 (M.op X1 X2)) X2)
       have r₂ := eq178 X0 X1 X2 (M.op (M.op X0 (M.op X1 X2)) X2)
       grind)
    | exact resolve eq13 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq2909 : ∀ X1 X2 X3 : G, (k X3 (M.op X1 (M.op X2 X3))) = X3 := by
    intro X1 X2 X3
    first
    | (have j0 := eq2785 x X1 X2 X3
       grind)
    | (have r₁ := eq2785 X3 x X1 X2
       have r₂ := eq1558 x X1 X2 X3 x
       grind)
    | exact resolve eq2785 eq1558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1558 eq2785
  have eq3150 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X1) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2909 x (M.op X0 X1) X1
       have i₂ := eq185 X0 X1 x
       grind)
    | exact superpose eq185 eq2909
    | exact resolve eq2909 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2909
  have eq3321 : ∀ X0 : G, (σ x) = (k (σ x) (σ (M.op (M.op X0 x) x))) := by
    intro X0
    first
    | (have i₁ := eq35 (M.op (M.op X0 x) x)
       have i₂ := eq3150 X0 x
       grind)
    | exact superpose eq3150 eq35
    | exact resolve eq35 eq3150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq3325 : ∀ X0 : G, (τ (σ x)) = (k x (τ (M.op (M.op X0 (σ x)) (σ x)))) := by
    intro X0
    first
    | (have i₁ := eq90 (M.op (M.op X0 sF2) sF2)
       have i₂ := eq3150 X0 sF2
       grind)
    | exact superpose eq3150 eq90
    | exact resolve eq90 eq3150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq3150
  have eq3328 : ∀ X0 : G, x = (k x (τ (M.op (M.op X0 (σ x)) (σ x)))) := by
    intro X0
    first
    | exact superpose eq29 eq3325
    | exact resolve eq3325 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3325
  have eq3332 : ∀ X0 : G, (σ x) = (k (σ x) (σ (M.op (M.op X0 x) x))) := by
    intro X0
    first
    | (have i₁ := eq3321 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3321
    | (have j0 := eq3321 X0
       grind)
    | exact resolve eq3321 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3321
  have eq4908 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2439 eq530
    | exact resolve eq530 eq2439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2439
  have eq4917 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq4908
       have r₂ := eq27
       grind)
    | exact resolve eq4908 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4908
  have eq4922 : x = (k x (τ (M.op (σ y) (σ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq4917 eq3328
    | exact resolve eq3328 eq4917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3328
  have eq4946 : x = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq4917 eq4922
    | exact resolve eq4922 eq4917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4917 eq4922
  have eq4950 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq4946
    | exact resolve eq4946 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4946
  have eq4952 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq4950
       have r₂ := eq13 x y
       grind)
    | exact resolve eq4950 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4950
  have eq4954 : x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq528
       have i₂ := eq4952
       grind)
    | exact superpose eq4952 eq528
    | exact resolve eq528 eq4952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528 eq4952
  have eq4958 : y = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4954
  have eq4995 : ∀ X0 : G, (M.op y x) = (M.op X0 (M.op y x)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq185 y x x
       have i₂ := eq4958
       grind)
    | exact superpose eq4958 eq185
    | exact resolve eq185 eq4958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq5004 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4958 eq4995
    | exact resolve eq4995 eq4958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4958 eq4995
  have eq5125 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5004 x
       grind)
    | exact superpose eq5004 eq18
    | (have j1 := eq5004 x
       grind)
    | exact resolve eq18 eq5004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5004
  have eq5142 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq5125
  have eq5154 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq5142 eq195
    | exact resolve eq195 eq5142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5287 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5154 eq26
    | (have j1 := eq5154 X0 (σ x)
       grind)
    | exact resolve eq26 eq5154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5154
  have eq5313 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5142 eq5287
    | exact resolve eq5287 eq5142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5142 eq5287
  have eq5401 : (τ (σ y)) = (k (τ (σ y)) y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5313 eq801
    | exact resolve eq801 eq5313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5313
  have eq5412 : y = (k y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq5401
    | exact resolve eq5401 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5401
  have eq5447 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq572 y y
       have i₂ := eq5412
       grind)
    | exact superpose eq5412 eq572
    | (have j0 := eq572 y y
       grind)
    | (have r₁ := eq572 y y
       have r₂ := eq5412
       grind)
    | exact resolve eq572 eq5412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5412
  have eq5448 : y ≠ y ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq5447
  have eq5449 : y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq5448
  have eq5459 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 y y x
       have i₂ := eq5449
       grind)
    | exact superpose eq5449 eq181
    | exact resolve eq181 eq5449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5613 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq5459 X0 x
       grind)
    | (have i₁ := eq18
       have i₂ := eq5459 x X0
       grind)
    | exact superpose eq5459 eq18
    | (have j1 := eq5459 X0 x
       grind)
    | exact resolve eq18 eq5459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5459
  have eq5706 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5449
       have i₂ := eq5613 y
       grind)
    | exact superpose eq5613 eq5449
    | exact resolve eq5449 eq5613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5449 eq5613
  have eq5725 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5706
  have eq5740 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5725
       grind)
    | exact superpose eq5725 eq18
    | exact resolve eq18 eq5725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5741 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq5725
       grind)
    | exact superpose eq5725 eq24
    | exact resolve eq24 eq5725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5788 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq5741
    | exact resolve eq5741 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5741
  have eq5789 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq179 eq5740
    | exact resolve eq5740 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5740
  have eq5790 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5725 eq5789
    | exact resolve eq5789 eq5725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5725 eq5789
  have eq5849 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5790 eq1290
    | exact resolve eq1290 eq5790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290 eq5790
  have eq5873 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq5849
    | exact resolve eq5849 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5849
  have eq5886 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5788 eq5873
    | exact resolve eq5873 eq5788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5873
  have eq6287 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5886 eq572
    | (have j0 := eq572 (σ y) (σ y)
       grind)
    | (have r₁ := eq572 (σ y) (σ y)
       have r₂ := eq5886
       grind)
    | exact resolve eq572 eq5886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5886
  have eq6288 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6287
  have eq6289 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6288
  have eq6308 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq6289 eq181
    | exact resolve eq181 eq6289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6452 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6308 eq26
    | (have j1 := eq6308 X0 (σ x)
       grind)
    | exact resolve eq26 eq6308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6453 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6308 eq6289
    | exact resolve eq6289 eq6308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6289 eq6308
  have eq6468 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq6453 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6453
  have eq6492 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6468 eq6452
    | (have j1 := eq6468 (σ x)
       grind)
    | exact resolve eq6452 eq6468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6452 eq6468
  have eq6518 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6492 eq27
    | exact resolve eq27 eq6492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6492
  have eq6558 : x = (M.op x y) := by
    first
    | (have r₁ := eq6518
       have r₂ := eq5788
       grind)
    | exact resolve eq6518 eq5788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5788 eq6518
  have eq6561 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6558
       grind)
    | exact superpose eq6558 eq18
    | exact resolve eq18 eq6558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6562 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq6558
       grind)
    | exact superpose eq6558 eq22
    | exact resolve eq22 eq6558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq6570 : ∀ X0 : G, (σ x) = (k (σ x) (σ (M.op (M.op X0 (M.op x y)) (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq3332 X0
       have i₂ := eq6558
       grind)
    | exact superpose eq6558 eq3332
    | exact resolve eq3332 eq6558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3332
  have eq6577 : (σ x) = (k (σ x) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq179 eq6570
    | exact resolve eq6570 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq6570
  have eq6580 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq6561 eq6577
    | exact resolve eq6577 eq6561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6577
  have eq6582 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq6580
    | exact resolve eq6580 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6580
  have eq6585 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq6562 eq20
    | exact resolve eq20 eq6562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6596 : ∀ X0 : G, (τ (k (σ x) X0)) = (k (M.op x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq6562 eq1239
    | exact resolve eq1239 eq6562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239
  have eq7245 : (M.op x y) = (k (M.op x y) y) := by
    first
    | exact superpose eq6561 eq599
    | exact resolve eq599 eq6561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq7311 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq6582 eq572
    | (have j0 := eq572 (σ x) (σ (M.op x y))
       grind)
    | exact resolve eq572 eq6582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6582
  have eq7313 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have r₁ := eq7311
       have r₂ := eq6585
       grind)
    | exact resolve eq7311 eq6585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7311
  have eq7319 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq6585 eq7313
    | exact resolve eq7313 eq6585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7313
  have eq7324 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq6585 eq7319
    | exact resolve eq7319 eq6585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7319
  have eq7325 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq7324
  have eq7514 : ∀ X0 X1 : G, (M.op X1 (σ x)) = (M.op X0 (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq7325 eq181
    | exact resolve eq181 eq7325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7608 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq7514 eq7325
    | exact resolve eq7325 eq7514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7325 eq7514
  have eq8903 : (k (M.op x y) (τ (σ y))) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq530 eq6596
    | exact resolve eq6596 eq530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530 eq6596
  have eq8966 : (k (M.op x y) y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq31 eq8903
    | exact resolve eq8903 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8903
  have eq8996 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq7245 eq8966
    | exact resolve eq8966 eq7245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7245 eq8966
  have eq9016 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7608 eq8996
    | exact resolve eq8996 eq7608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8996
  have eq9721 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9016 eq14
    | exact resolve eq14 eq9016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9016
  have eq9732 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9721
    | exact resolve eq9721 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq9721
  have eq9737 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq9732
       have r₂ := eq27
       grind)
    | exact resolve eq9732 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9732
  have eq9743 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq9737 eq195
    | exact resolve eq195 eq9737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq9929 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq9743 eq26
    | (have j1 := eq9743 X0 (σ x)
       grind)
    | exact resolve eq26 eq9743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9743
  have eq9956 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq9737 eq9929
    | exact resolve eq9929 eq9737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9737 eq9929
  have eq10062 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq9956 eq801
    | exact resolve eq801 eq9956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801 eq9956
  have eq10074 : y = (k y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq31 eq10062
    | exact resolve eq10062 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10062
  have eq10113 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq572 y y
       have i₂ := eq10074
       grind)
    | exact superpose eq10074 eq572
    | (have j0 := eq572 y y
       grind)
    | (have r₁ := eq572 y y
       have r₂ := eq10074
       grind)
    | exact resolve eq572 eq10074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq10074
  have eq10114 : y ≠ y ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq10113
  have eq10115 : y = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq10114
  have eq10133 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 y y x
       have i₂ := eq10115
       grind)
    | exact superpose eq10115 eq181
    | exact resolve eq181 eq10115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq10335 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq10115
       have i₂ := eq10133 X0 y
       grind)
    | (have i₁ := eq10115
       have i₂ := eq10133 y X0
       grind)
    | exact superpose eq10133 eq10115
    | exact resolve eq10115 eq10133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10115
  have eq10354 : ∀ X0 : G, (M.op x y) = (M.op X0 y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq6561
       have i₂ := eq10133 X0 sF0
       grind)
    | (have i₁ := eq6561
       have i₂ := eq10133 sF0 x
       grind)
    | exact superpose eq10133 eq6561
    | (have j1 := eq10133 X0 x
       grind)
    | exact resolve eq6561 eq10133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6561 eq10133
  have eq10355 : ∀ X0 : G, y = (M.op X0 y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq10335 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10335
  have eq10375 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10354 eq10355
    | (have j0 := eq10355 x
       grind)
    | exact resolve eq10355 eq10354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10354 eq10355
  have eq10458 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10375 eq31
    | exact resolve eq31 eq10375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq10375
  have eq10570 : x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq10458
    | exact resolve eq10458 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq10458
  have eq10594 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10570
       have i₂ := eq6558
       grind)
    | exact superpose eq6558 eq10570
    | exact resolve eq10570 eq6558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6558 eq10570
  have eq10595 : y = (M.op x y) := by grind
  clear eq10594
  have eq10611 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq10595
       grind)
    | exact superpose eq10595 eq24
    | exact resolve eq24 eq10595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq10595
  have eq10665 : (σ x) = (σ y) := by
    first
    | exact superpose eq6562 eq10611
    | exact resolve eq10611 eq6562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6562 eq10611
  have eq10666 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10665 eq26
    | exact resolve eq26 eq10665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq10665
  have eq10771 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7608 eq10666
    | exact resolve eq10666 eq7608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7608 eq10666
  have eq10815 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq10771 eq27
    | exact resolve eq27 eq10771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq10771
  have eq10886 : False := by grind
  exact eq10886

/-- `Equation4542`: `x ◇ (y ◇ z) = (z ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_x_pxy_Equation4542 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4542 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4542.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X0) X2) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
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
  have eq60 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq115 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq48 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq48
    | (have j0 := eq48 x
       grind)
    | exact resolve eq48 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq48
    | (have j0 := eq48 (M.op x y)
       grind)
    | exact resolve eq48 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq142 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq60 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq60
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
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
  have eq175 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X0) X2) (M.op X3 X0)) = (M.op X2 (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X2 X1 (M.op X3 X0)
       have i₂ := eq16 X1 X3 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op X2 X0) X2
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X3 X1)) = (M.op (M.op (M.op X0 X1) X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X2 X0) X3 X1
       have i₂ := eq16 X1 X2 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op y (M.op X0 x)) = (M.op (M.op x y) x) := by
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
  have eq181 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq16 X0 X3 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op X3 X0) X2) (M.op X3 X0)) = (M.op (M.op X0 X2) X0) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq175 X0 x X2 X3
       have i₂ := eq16 X2 (M.op X0 x) X0
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq187 : y ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq570 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq182 X0 X1 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq182
    | (have j0 := eq182 X0 X1 y x
       grind)
    | exact resolve eq182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq182
    | (have j0 := eq182 X0 X1 (σ y) (σ x)
       grind)
    | exact resolve eq182 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq603 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq570 X0 x
       grind)
    | (have i₁ := eq16 X0 x y
       have i₂ := eq570 X0 x
       grind)
    | exact superpose eq570 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq605 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op x y))) = (M.op X1 (M.op X3 (M.op X2 y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq182 X1 X0 (M.op X2 y) X3
       have i₂ := eq570 X0 X2
       grind)
    | (have i₁ := eq182 X1 X3 (M.op x y) X0
       have i₂ := eq570 X3 X2
       grind)
    | exact superpose eq570 eq182
    | exact resolve eq182 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq612 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op x y))) = (M.op (M.op y X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq605 X0 X1 x x
       have i₂ := eq176 x x y X1
       grind)
    | exact superpose eq176 eq605
    | (have j1 := eq176 X0 x y X1
       grind)
    | exact resolve eq605 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq605
  have eq617 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op x y))) = (M.op X1 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq612 X0 X1
       have i₂ := eq603 X1
       grind)
    | exact superpose eq603 eq612
    | exact resolve eq612 eq603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603 eq612
  have eq627 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq572 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq672 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq617 eq16
    | exact resolve eq16 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq677 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op x y))) = (M.op (M.op (M.op X2 (M.op x y)) X1) (M.op X2 (M.op x y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq617 eq16
    | exact resolve eq16 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 (M.op x y))) = (M.op (M.op (M.op X2 (M.op x y)) X1) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq617 eq677
    | exact resolve eq677 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq685 : ∀ X1 X2 : G, (M.op X1 (M.op x y)) = (M.op (M.op (M.op X2 (M.op x y)) X1) (M.op x y)) := by
    intro X1 X2
    first
    | exact superpose eq617 eq682
    | exact resolve eq682 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617 eq682
  have eq840 : (M.op x y) = (k x y) ∨ y = (M.op x y) := by
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
  have eq843 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq849 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (k X0 X1) X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq883 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq933 : y ≠ (M.op x y) ∨ x = (M.op y x) ∨ x = (k x y) := by
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
  have eq936 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq949 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq840
       grind)
    | exact superpose eq840 eq41
    | exact resolve eq41 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840
  have eq950 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq949
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq949
    | exact resolve eq949 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq949
  have eq952 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq950
    | exact resolve eq950 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq950
  have eq960 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq952 eq843
    | exact resolve eq843 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq967 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq960
       have r₂ := eq27
       grind)
    | exact resolve eq960 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq972 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq967 eq188
    | (have r₁ := eq188
       have r₂ := eq967
       grind)
    | exact resolve eq188 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq973 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq967 eq27
    | exact resolve eq27 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq974 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq972
  have eq976 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (k (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq974 eq627
    | exact resolve eq627 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq977 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (k (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq974 eq181
    | exact resolve eq181 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq985 : (M.op (σ y) (σ x)) = (M.op (σ y) (k (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq967 eq977
    | exact resolve eq977 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq986 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq967 eq976
    | exact resolve eq976 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976
  have eq988 : (k (σ y) (σ x)) = (M.op (σ y) (k (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq974 eq985
    | exact resolve eq985 eq974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974 eq985
  have eq989 : (M.op (σ x) (σ y)) = (M.op (k (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq986
    | exact resolve eq986 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986
  have eq991 : (σ y) = (M.op (k (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq967 eq989
    | exact resolve eq989 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq1012 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (M.op (k (σ y) (σ x)) (σ y)) = (k (k (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq988 eq13
    | (have j0 := eq13 (k (σ y) (σ x)) (σ y)
       grind)
    | (have r₁ := eq13 (k (σ y) (σ x)) (σ y)
       have r₂ := eq988
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq988
       grind)
    | exact resolve eq13 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq1016 : (M.op (k (σ y) (σ x)) (σ y)) = (k (k (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1012
  have eq1019 : (σ y) = (k (k (σ y) (σ x)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq991 eq1016
    | exact resolve eq1016 eq991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq991 eq1016
  have eq1020 : (τ (σ y)) = (k (τ (k (σ y) (σ x))) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1019 eq153
    | exact resolve eq153 eq1019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq1019
  have eq1021 : (τ (σ y)) = (k (k y x) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq115 eq1020
    | exact resolve eq1020 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1022 : y = (k (k y x) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32 eq1021
    | exact resolve eq1021 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021
  have eq1497 : y ≠ y ∨ y = (M.op (k y x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq883 (k y x) y
       have i₂ := eq1022
       grind)
    | exact superpose eq1022 eq883
    | (have j0 := eq883 (k y x) y
       grind)
    | (have r₁ := eq883 (k y x) y
       have r₂ := eq1022
       grind)
    | exact resolve eq883 eq1022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1510 : y = (M.op (k y x) y) ∨ y = (M.op x y) := by grind
  clear eq1497
  have eq1548 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq570 X0 (k y x)
       have i₂ := eq1510
       grind)
    | exact superpose eq1510 eq570
    | exact resolve eq570 eq1510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq1578 : y = (M.op (k y x) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1510
       have i₂ := eq1548 (k y x)
       grind)
    | exact superpose eq1548 eq1510
    | exact resolve eq1510 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1510
  have eq1579 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq1548 x
       grind)
    | (have i₁ := eq18
       have i₂ := eq1548 x
       grind)
    | exact superpose eq1548 eq18
    | (have j1 := eq1548 x
       grind)
    | exact resolve eq18 eq1548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1548
  have eq1585 : y = (M.op (k y x) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq1578
  have eq1598 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op (M.op x y) x) ∨ x = (k x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1579 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq1579
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1579
       grind)
    | exact resolve eq12 eq1579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1579
  have eq1604 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ y = (M.op x y) := by grind
  clear eq1598
  have eq2543 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq967 eq936
    | (have r₁ := eq936
       have r₂ := eq967
       grind)
    | exact resolve eq936 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq936
  have eq2544 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2543
  have eq2545 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq952 eq2544
    | exact resolve eq2544 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2544
  have eq2556 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2545 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2545
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2545
       grind)
    | exact resolve eq13 eq2545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2545
  have eq2561 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq2556
  have eq2570 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2561
    | exact resolve eq2561 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2561
  have eq2576 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq952 eq2570
    | exact resolve eq2570 eq952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq952 eq2570
  have eq2580 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2576
       have r₂ := eq27
       grind)
    | exact resolve eq2576 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2576
  have eq2583 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2580 eq29
    | exact resolve eq29 eq2580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq2584 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ x) (σ X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2580 eq51
    | exact resolve eq51 eq2580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq2587 : (k y (M.op x y)) = (τ (k (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2580 eq117
    | exact resolve eq117 eq2580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq2593 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2580 eq973
    | exact resolve eq973 eq2580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq973
  have eq2620 : (σ x) ≠ (σ y) ∨ y = (M.op x y) := by grind
  clear eq2593
  have eq2628 : (k y x) = (k y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq115 eq2587
    | exact resolve eq2587 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq2587
  have eq2631 : ∀ X0 : G, (k x X0) = (k (M.op x y) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq45 eq2584
    | exact resolve eq2584 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq2584
  have eq2632 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq2583
    | exact resolve eq2583 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2583
  have eq2638 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2632
       grind)
    | exact superpose eq2632 eq24
    | exact resolve eq24 eq2632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2652 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq2638
    | exact resolve eq2638 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2638
  have eq2746 : y = (M.op (k y (M.op x y)) (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1585
       have i₂ := eq2628
       grind)
    | exact superpose eq2628 eq1585
    | exact resolve eq1585 eq2628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1585 eq2628
  have eq2757 : y = (M.op (k y (M.op x y)) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq2746
  have eq2841 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1604
       have i₂ := eq2631 sF0
       grind)
    | exact superpose eq2631 eq1604
    | exact resolve eq1604 eq2631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604 eq2631
  have eq2856 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ y = (M.op x y) := by grind
  clear eq2841
  have eq2875 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2632 eq2856
    | exact resolve eq2856 eq2632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2856
  have eq2885 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2632 eq2875
    | exact resolve eq2875 eq2632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2632 eq2875
  have eq2891 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq883 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq2885
       have r₂ := eq883 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq2885 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2885
  have eq3191 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (M.op x y)) X1) (M.op x y)) = (M.op (M.op X0 X1) y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2757 eq178
    | exact resolve eq178 eq2757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3642 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op X0 X1) y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq685 eq3191
    | exact resolve eq3191 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685 eq3191
  have eq3997 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op X1 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq178 X1 X0 (M.op x X0) x
       have i₂ := eq184 X0 X1 x
       grind)
    | exact superpose eq184 eq178
    | exact resolve eq178 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq4964 : (M.op (M.op x y) (M.op x y)) = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2757 eq3642
    | exact resolve eq3642 eq2757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2757 eq3642
  have eq5042 : (M.op (M.op x y) (M.op x y)) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq4964
  have eq5097 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2891 eq5042
    | exact resolve eq5042 eq2891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2891 eq5042
  have eq5171 : (M.op x y) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq5097
       grind)
    | exact superpose eq5097 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq5097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq5097
  have eq5183 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by grind
  clear eq5171
  have eq6352 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq5183
       grind)
    | exact superpose eq5183 eq41
    | exact resolve eq41 eq5183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5183
  have eq6357 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6352
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6352
    | exact resolve eq6352 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6352
  have eq6360 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq6357
    | exact resolve eq6357 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6357
  have eq6362 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2580 eq6360
    | exact resolve eq6360 eq2580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2580 eq6360
  have eq6367 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq6362 eq849
    | (have j0 := eq849 (σ y) (σ y) x
       grind)
    | exact resolve eq849 eq6362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6370 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq572 eq6367
    | (have j0 := eq6367 (σ x)
       grind)
    | exact resolve eq6367 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6367
  have eq6374 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq6370
    | exact resolve eq6370 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6370
  have eq6378 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq967 eq6374
    | exact resolve eq6374 eq967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq967 eq6374
  have eq6379 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6378
  have eq6388 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6379 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq6379
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq6379
       grind)
    | exact resolve eq13 eq6379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6379
  have eq6399 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6388
  have eq6408 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6362 eq6399
    | exact resolve eq6399 eq6362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6362 eq6399
  have eq6410 : y = (M.op x y) := by
    first
    | (have r₁ := eq6408
       have r₂ := eq2620
       grind)
    | exact resolve eq6408 eq2620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2620 eq6408
  have eq6412 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq6410
       grind)
    | exact superpose eq6410 eq18
    | exact resolve eq18 eq6410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6413 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq6410
       grind)
    | exact superpose eq6410 eq24
    | exact resolve eq24 eq6410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq6415 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq6410
       grind)
    | exact superpose eq6410 eq41
    | exact resolve eq41 eq6410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq6417 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq187
       have i₂ := eq6410
       grind)
    | exact superpose eq6410 eq187
    | (have r₁ := eq187
       have r₂ := eq6410
       grind)
    | exact resolve eq187 eq6410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq6421 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op (M.op x y) x) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq933
       have i₂ := eq6410
       grind)
    | exact superpose eq6410 eq933
    | (have r₁ := eq933
       have r₂ := eq6410
       grind)
    | exact resolve eq933 eq6410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq6422 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq6421
  have eq6423 : (k (M.op x y) x) = (M.op (M.op x y) x) := by grind
  clear eq6417
  have eq6426 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq6413 eq20
    | exact resolve eq20 eq6413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7102 : (M.op x (M.op x y)) = (M.op (k (M.op x y) x) (M.op x y)) := by
    first
    | exact superpose eq6423 eq672
    | exact resolve eq672 eq6423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672
  have eq7105 : (k (M.op x y) x) = (M.op y (k (M.op x y) x)) := by
    first
    | exact superpose eq6423 eq180
    | exact resolve eq180 eq6423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq7127 : (k (M.op x y) x) = (M.op (M.op x y) (k (M.op x y) x)) := by
    first
    | (have i₁ := eq7105
       have i₂ := eq6410
       grind)
    | exact superpose eq6410 eq7105
    | exact resolve eq7105 eq6410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7105
  have eq7128 : (M.op x y) = (M.op (k (M.op x y) x) (M.op x y)) := by
    first
    | exact superpose eq6412 eq7102
    | exact resolve eq7102 eq6412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6412 eq7102
  have eq7524 : (k (M.op x y) x) ≠ (k (M.op x y) x) ∨ (M.op (k (M.op x y) x) (M.op x y)) = (k (k (M.op x y) x) (M.op x y)) := by
    first
    | exact superpose eq7127 eq13
    | (have j0 := eq13 (k (M.op x y) x) (M.op x y)
       grind)
    | (have r₁ := eq13 (k (M.op x y) x) (M.op x y)
       have r₂ := eq7127
       grind)
    | exact resolve eq13 eq7127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7127
  have eq7536 : (M.op (k (M.op x y) x) (M.op x y)) = (k (k (M.op x y) x) (M.op x y)) := by grind
  clear eq7524
  have eq7541 : (M.op x y) = (k (k (M.op x y) x) (M.op x y)) := by
    first
    | exact superpose eq7128 eq7536
    | exact resolve eq7536 eq7128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7128 eq7536
  have eq7544 : (σ (M.op x y)) = (k (σ (k (M.op x y) x)) (σ y)) := by
    first
    | exact superpose eq7541 eq6415
    | exact resolve eq6415 eq7541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7541
  have eq7554 : (σ (M.op x y)) = (k (k (σ (M.op x y)) (σ x)) (σ y)) := by
    first
    | (have i₁ := eq7544
       have i₂ := eq40 sF0
       grind)
    | exact superpose eq40 eq7544
    | exact resolve eq7544 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq7544
  have eq7556 : (σ (M.op x y)) = (k (k (σ (M.op x y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq20 eq7554
    | exact resolve eq7554 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7554
  have eq7558 : (σ y) = (k (k (σ y) (σ x)) (σ y)) := by
    first
    | exact superpose eq6426 eq7556
    | exact resolve eq7556 eq6426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7556
  have eq7566 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (k (σ y) (σ x)) (σ y)) := by
    first
    | exact superpose eq7558 eq883
    | (have j0 := eq883 (k (σ y) (σ x)) (σ y)
       grind)
    | (have r₁ := eq883 (k (σ y) (σ x)) (σ y)
       have r₂ := eq7558
       grind)
    | exact resolve eq883 eq7558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7567 : (σ y) = (M.op (k (σ y) (σ x)) (σ y)) := by grind
  clear eq7566
  have eq7579 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op X0 (σ y))) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq7567 eq849
    | (have j0 := eq849 (σ y) (σ x) x
       grind)
    | exact resolve eq849 eq7567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq7583 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq7567 eq572
    | exact resolve eq572 eq7567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7592 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 (σ y)) X1) (σ y)) = (M.op (M.op X0 X1) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq7567 eq178
    | exact resolve eq178 eq7567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq7605 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) (σ y)) = (M.op (M.op X0 X1) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq7592 X0 X1
       have i₂ := eq3997 sF3 X1
       grind)
    | exact superpose eq3997 eq7592
    | exact resolve eq7592 eq3997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3997 eq7592
  have eq7611 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq572 eq7579
    | (have j0 := eq7579 (σ x)
       grind)
    | exact resolve eq7579 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq7579
  have eq7613 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op X0 X1) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq627 eq7605
    | exact resolve eq7605 eq627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7605
  have eq7616 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq7583 eq7611
    | exact resolve eq7611 eq7583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7611
  have eq7618 : ∀ X0 X1 : G, (M.op X1 (σ y)) = (M.op (M.op X0 X1) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq7583 eq7613
    | exact resolve eq7613 eq7583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7613
  have eq7620 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq7616
    | exact resolve eq7616 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7616
  have eq7660 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq7583 eq627
    | exact resolve eq627 eq7583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq7662 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq7618 eq7660
    | exact resolve eq7660 eq7618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7618 eq7660
  have eq7685 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq7583 eq7662
    | exact resolve eq7662 eq7583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7583 eq7662
  have eq7763 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7620 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq7620
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq7620
       grind)
    | exact resolve eq12 eq7620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7620
  have eq7777 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7763
  have eq7783 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq7777
    | exact resolve eq7777 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7777
  have eq7784 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7783
  have eq7809 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7784 eq7558
    | exact resolve eq7558 eq7784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7558
  have eq7810 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7784 eq7567
    | exact resolve eq7567 eq7784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7567
  have eq7814 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq7784 eq142
    | exact resolve eq142 eq7784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq7784
  have eq7819 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq7814
    | exact resolve eq7814 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq7814
  have eq7823 : (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7819
       have i₂ := eq6410
       grind)
    | exact superpose eq6410 eq7819
    | exact resolve eq7819 eq6410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6410 eq7819
  have eq9583 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq6422 eq6415
    | exact resolve eq6415 eq6422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6415 eq6422
  have eq9589 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq9583
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq9583
    | exact resolve eq9583 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9583
  have eq9594 : (σ x) = (k (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq6423 eq9589
    | exact resolve eq9589 eq6423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6423 eq9589
  have eq9606 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq9594 eq843
    | exact resolve eq843 eq9594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9613 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq9594 eq883
    | (have j0 := eq883 (σ x) (σ y)
       grind)
    | (have r₁ := eq883 (M.op x y) x
       have r₂ := eq9594
       grind)
    | exact resolve eq883 eq9594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883 eq9594
  have eq9614 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq26 eq9613
    | exact resolve eq9613 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9613
  have eq9620 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7823 eq9606
    | exact resolve eq9606 eq7823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9606
  have eq9622 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7823 eq9614
    | exact resolve eq9614 eq7823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7823 eq9614
  have eq9630 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9620 eq27
    | exact resolve eq27 eq9620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9620
  have eq9638 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9630
       have r₂ := eq2652
       grind)
    | exact resolve eq9630 eq2652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2652 eq9630
  have eq9641 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9638 eq27
    | exact resolve eq27 eq9638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9651 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9638 eq7685
    | exact resolve eq7685 eq9638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7685
  have eq9663 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq9651
    | exact resolve eq9651 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq9651
  have eq9666 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6426 eq9641
    | exact resolve eq9641 eq6426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6426 eq9641
  have eq9667 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9638 eq9663
    | exact resolve eq9663 eq9638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9663
  have eq9672 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9667 eq7810
    | exact resolve eq7810 eq9667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7810 eq9667
  have eq9718 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq9672
       have r₂ := eq9622
       grind)
    | exact resolve eq9672 eq9622
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9622 eq9672
  have eq9734 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9638 eq9718
    | exact resolve eq9718 eq9638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9638 eq9718
  have eq9742 : x = (M.op x y) := by
    first
    | (have r₁ := eq9734
       have r₂ := eq9666
       grind)
    | exact resolve eq9734 eq9666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9666 eq9734
  have eq9747 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq9742
       grind)
    | exact superpose eq9742 eq22
    | exact resolve eq22 eq9742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq9742
  have eq9790 : (σ x) = (σ y) := by
    first
    | exact superpose eq9747 eq6413
    | exact resolve eq6413 eq9747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6413
  have eq9791 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq9747 eq20
    | exact resolve eq20 eq9747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq9747
  have eq9834 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9790 eq843
    | exact resolve eq843 eq9790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq9882 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9790 eq7809
    | exact resolve eq7809 eq9790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7809 eq9790
  have eq9894 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9882 eq9834
    | exact resolve eq9834 eq9882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9834 eq9882
  have eq9895 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq9894
  have eq9968 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq9895 eq27
    | exact resolve eq27 eq9895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq9895
  have eq9986 : False := by grind
  exact eq9986

/-- `Equation4554`: `x ◇ (y ◇ z) = (z ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyy_pxy_pyx_Equation4554 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4554 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4554.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X3) X2) := by
    intro X0 X1 X2 X3
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq53 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X0 X4) X0) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq9 x x X0 X4
       have i₂ := eq9 x x X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X4 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X0 X1 X2 x
       have i₂ := eq9 X3 X4 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X2 X4) X2) = (M.op (M.op (M.op X0 X1) X0) X2) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq53 X2 (M.op x X0) X4
       have i₂ := eq9 X2 x X0 X1
       grind)
    | exact superpose eq9 eq53
    | exact resolve eq53 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq218 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq218 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq218 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq218 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq222 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq219 (σ X0)
       grind)
    | exact superpose eq219 eq15
    | exact resolve eq15 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq219 (τ X0)
       grind)
    | exact superpose eq219 eq18
    | exact resolve eq18 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq226 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq226
    | exact resolve eq226 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq233 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq222 X0
       have i₂ := eq219 X0
       grind)
    | exact superpose eq219 eq222
    | exact resolve eq222 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq237 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq229 X0
       have i₂ := eq219 X0
       grind)
    | exact superpose eq219 eq229
    | exact resolve eq229 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq229
  have eq251 : ∀ X0 X1 X2 X3 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op X2 (M.op X3 (σ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq57 X1 (σ X0) (σ X0) X2 X3
       have i₂ := eq233 X0
       grind)
    | exact superpose eq233 eq57
    | exact resolve eq57 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq270 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq277 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq270 X0 X1
       have i₂ := eq233 X0
       grind)
    | exact superpose eq233 eq270
    | (have j0 := eq270 X0 X1
       grind)
    | exact resolve eq270 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq1405 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq277 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq277 X0 X1
       grind)
    | exact superpose eq277 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq277 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq277 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq277 X0 X1
       grind)
    | exact resolve eq13 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq1465 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1405 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1405
  have eq1475 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1465 X0 X1
       have i₂ := eq233 X0
       grind)
    | exact superpose eq233 eq1465
    | (have j0 := eq1465 X0 X1
       grind)
    | exact resolve eq1465 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq1476 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1475 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475
  have eq1487 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1476 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1476
    | (have j0 := eq1476 X0 X1
       grind)
    | exact resolve eq1476 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476
  have eq1488 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1487 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1487
  have eq1685 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq251 X0 (σ (M.op X0 X0)) X1 X2
       have i₂ := eq233 (M.op X0 X0)
       grind)
    | exact superpose eq233 eq251
    | exact resolve eq251 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq40688 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1488 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1488
    | exact resolve eq1488 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40733 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1488 x y
       grind)
    | exact superpose eq1488 eq16
    | (have j1 := eq1488 x x
       grind)
    | exact resolve eq16 eq1488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq40953 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40688 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq40688
    | (have j0 := eq40688 X0 X1
       grind)
    | exact resolve eq40688 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq40688
  have eq40968 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq40953 X0 X1
       have i₂ := eq237 X0
       grind)
    | exact superpose eq237 eq40953
    | (have j0 := eq40953 X0 X1
       grind)
    | exact resolve eq40953 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237 eq40953
  have eq40976 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq40968 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq40968
    | (have j0 := eq40968 X1 X1
       grind)
    | exact resolve eq40968 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40968
  have eq61862 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X3 (σ X0))) = (σ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1685 X0 X2 X3
       have i₂ := eq9 (M.op X0 X0) X0 X0 X1
       grind)
    | exact superpose eq9 eq1685
    | exact resolve eq1685 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1685
  have eq62538 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X2) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61862 X0 X2 X1 (σ X0)
       have i₂ := eq233 X0
       grind)
    | exact superpose eq233 eq61862
    | exact resolve eq61862 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq62555 : ∀ X0 X1 X4 : G, (M.op (M.op (σ X0) X1) (σ X0)) = (σ (M.op (M.op X0 X4) X0)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq61862 X0 X4 x x
       have i₂ := eq9 x x (σ X0) X1
       grind)
    | exact superpose eq9 eq61862
    | exact resolve eq61862 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61862
  have eq192887 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq40733
       have i₂ := eq40976 y x
       grind)
    | exact superpose eq40976 eq40733
    | (have j1 := eq40976 x x
       grind)
    | exact resolve eq40733 eq40976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40733 eq40976
  have eq192890 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq192887
  have eq192926 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq192890
       grind)
    | exact superpose eq192890 eq10
    | exact resolve eq10 eq192890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192890
  have eq193016 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq192926
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq192926
    | exact resolve eq192926 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192926
  have eq193017 : x = (M.op x x) := by grind
  clear eq193016
  have eq193113 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x x) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq69 x x X0 X1
       have i₂ := eq193017
       grind)
    | exact superpose eq193017 eq69
    | exact resolve eq69 eq193017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq193305 : ∀ X0 : G, (σ (M.op x x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq62538 x x x
       have i₂ := eq193017
       grind)
    | exact superpose eq193017 eq62538
    | exact resolve eq62538 eq193017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62538
  have eq193352 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq193305 X0
       have i₂ := eq193017
       grind)
    | exact superpose eq193017 eq193305
    | exact resolve eq193305 eq193017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193305
  have eq193425 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq193113 X0 X1
       have i₂ := eq193017
       grind)
    | exact superpose eq193017 eq193113
    | exact resolve eq193113 eq193017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193017 eq193113
  have eq214372 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq193425 X0 (σ x)
       have i₂ := eq193352 X0
       grind)
    | exact superpose eq193352 eq193425
    | exact resolve eq193425 eq193352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193352
  have eq214934 : ∀ X0 X2 : G, (σ (M.op (M.op X0 X2) X0)) = (M.op x (σ X0)) := by
    intro X0 X2
    first
    | (have i₁ := eq62555 X0 x X2
       have i₂ := eq193425 (σ X0) x
       grind)
    | exact superpose eq193425 eq62555
    | exact resolve eq62555 eq193425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62555
  have eq215584 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq214934 X0 x
       have i₂ := eq193425 X0 x
       grind)
    | exact superpose eq193425 eq214934
    | exact resolve eq214934 eq193425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193425 eq214934
  have eq215824 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq214372 (σ y)
       grind)
    | exact superpose eq214372 eq16
    | exact resolve eq16 eq214372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214372
  have eq234871 : False := by grind
  exact eq234871

/-- `Equation4554`: `x ◇ (y ◇ z) = (z ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxy_pyx_Equation4554 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4554 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4554.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X3) X2) := by
    intro X0 X1 X2 X3
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
  have eq52 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X5) X2) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X3 (M.op X2 x) X2 X5
       have i₂ := eq14 X0 X1 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op y X1) y) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X4 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X0 X1 X2 x
       have i₂ := eq14 X3 X4 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq80 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq82 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq84 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq82 (σ X0)
       grind)
    | exact superpose eq82 eq10
    | exact resolve eq10 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq82 sF2
       grind)
    | exact superpose eq82 eq50
    | exact resolve eq50 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq87 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq86
       have i₂ := eq82 x
       grind)
    | exact superpose eq82 eq86
    | exact resolve eq86 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq89 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq84
    | exact resolve eq84 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq96 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq80
       have i₂ := eq82 sF3
       grind)
    | exact superpose eq82 eq80
    | exact resolve eq80 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq97 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq96
       have i₂ := eq82 y
       grind)
    | exact superpose eq82 eq96
    | exact resolve eq96 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq79
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq79
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq79 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq104
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq104
    | exact resolve eq104 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq109
    | exact resolve eq109 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq137 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq140 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq137
       have i₂ := eq82 sF1
       grind)
    | exact superpose eq82 eq137
    | exact resolve eq137 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq142 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq140
       have i₂ := eq82 sF0
       grind)
    | exact superpose eq82 eq140
    | exact resolve eq140 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq235 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op X2 (M.op x y)) := by
    intro X0 X2
    first
    | (have i₁ := eq53 X2 x
       have i₂ := eq53 X0 x
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq236 : ∀ X0 X1 X3 : G, (M.op X3 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq53 X3 x
       have i₂ := eq14 X0 X1 y x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq235 eq142
    | exact resolve eq142 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq235
  have eq305 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq270 (M.op sF0 x)
       have i₂ := eq14 X0 X1 sF0 x
       grind)
    | exact superpose eq14 eq270
    | exact resolve eq270 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq317 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq59 x x
       have i₂ := eq14 x x x X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq321 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op x y) x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 X2 (M.op x x)
       have i₂ := eq59 X2 x
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq324 : ∀ X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op (M.op x y) x) y) := by
    intro X1
    first
    | (have i₁ := eq53 X1 (M.op x x)
       have i₂ := eq59 y x
       grind)
    | exact superpose eq59 eq53
    | exact resolve eq53 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq325 : ∀ X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq54 x (M.op X1 x)
       have i₂ := eq59 sF3 X1
       grind)
    | exact superpose eq59 eq54
    | exact resolve eq54 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq340 : ∀ X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    intro X1
    first
    | exact superpose eq60 eq54
    | exact resolve eq54 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq511 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | exact superpose eq236 eq270
    | exact resolve eq270 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq533 : (σ (M.op (k x x) (k x x))) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq89 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq89
    | exact resolve eq89 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq548 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op (k x x) (k x x))) := by
    first
    | (have i₁ := eq533
       have i₂ := eq82 sF2
       grind)
    | exact superpose eq82 eq533
    | exact resolve eq533 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq550 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq548
       have i₂ := eq82 x
       grind)
    | exact superpose eq82 eq548
    | exact resolve eq548 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq548
  have eq552 : (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | exact superpose eq60 eq550
    | exact resolve eq550 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq550
  have eq553 : (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq552
       have i₂ := eq59 (M.op x x) x
       grind)
    | exact superpose eq59 eq552
    | exact resolve eq552 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq749 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op (M.op x y) x) y)) := by
    first
    | exact superpose eq324 eq270
    | exact resolve eq270 eq324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq324
  have eq792 : ∀ X0 X1 X2 X3 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op X2 (M.op X3 (σ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X1 (σ X0) (σ X0) X2 X3
       have i₂ := eq89 X0
       grind)
    | exact superpose eq89 eq61
    | exact resolve eq61 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq937 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X0))) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq52 X3 X4 X0 X2 (M.op x x)
       have i₂ := eq59 X0 x
       grind)
    | exact superpose eq59 eq52
    | exact resolve eq52 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1160 : (M.op (M.op (M.op x y) x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq325 eq340
    | exact resolve eq340 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325 eq340
  have eq4827 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op (M.op X0 (M.op X1 (M.op x y))) (M.op X0 (M.op X1 (M.op x y))))) := by
    intro X0 X1
    first
    | exact superpose eq305 eq89
    | exact resolve eq89 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq4834 : ∀ X1 : G, (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op (M.op (M.op x y) x) (M.op X1 (M.op x y)))) := by
    intro X1
    first
    | (have i₁ := eq4827 X1 X1
       have i₂ := eq321 (M.op X1 (M.op X1 sF0)) X1 (M.op X1 sF0)
       grind)
    | exact superpose eq321 eq4827
    | exact resolve eq4827 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4827
  have eq4842 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq305 eq4834
    | exact resolve eq4834 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305 eq4834
  have eq4843 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op x y) x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq4842
       have i₂ := eq321 (M.op sF1 sF1) sF1 sF1
       grind)
    | exact superpose eq321 eq4842
    | exact resolve eq4842 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4842
  have eq5173 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (M.op X1 (σ (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq321 eq4843
    | exact resolve eq4843 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321 eq4843
  have eq12208 : ∀ X0 X1 X2 : G, (M.op X0 (σ (M.op (M.op y y) (M.op y y)))) = (M.op X1 (M.op X2 (M.op (σ y) (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq792 (M.op y y) X0 X1 X2
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq792
    | exact resolve eq792 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq792
  have eq12450 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op X1 (M.op X2 (M.op (σ y) (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12208 X0 X1 X2
       have i₂ := eq511 (M.op y y) y
       grind)
    | exact superpose eq511 eq12208
    | exact resolve eq12208 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511 eq12208
  have eq12492 : ∀ X1 X2 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X1 (M.op X2 (M.op (σ y) (σ y)))) := by
    intro X1 X2
    first
    | exact superpose eq5173 eq12450
    | exact resolve eq12450 eq5173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5173 eq12450
  have eq37617 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op x y) x) (σ y)) := by
    first
    | (have i₁ := eq12492 x x
       have i₂ := eq937 sF3 x x sF3
       grind)
    | exact superpose eq937 eq12492
    | exact resolve eq12492 eq937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq937 eq12492
  have eq64242 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq110 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq64250 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq64242
    | exact resolve eq64242 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64242
  have eq64255 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq64250
       have r₂ := eq28
       grind)
    | exact resolve eq64250 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64250
  have eq64257 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq64255 eq87
    | exact resolve eq87 eq64255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64255
  have eq64344 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq64257
    | exact resolve eq64257 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64257
  have eq64345 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq64344
  have eq64355 : (M.op (M.op x y) x) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq317 x
       have i₂ := eq64345
       grind)
    | exact superpose eq64345 eq317
    | exact resolve eq317 eq64345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq64358 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq59 X0 x
       have i₂ := eq64345
       grind)
    | exact superpose eq64345 eq59
    | exact resolve eq59 eq64345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq64873 : ∀ X0 : G, (M.op x x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq64355
       have i₂ := eq64358 sF0
       grind)
    | exact superpose eq64358 eq64355
    | exact resolve eq64355 eq64358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64355 eq64358
  have eq65061 : ∀ X0 : G, (M.op x x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq64873 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64873
  have eq66972 : ∀ X0 : G, x = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq64345
       have i₂ := eq65061 X0
       grind)
    | (have i₁ := eq64345
       have i₂ := eq65061 x
       grind)
    | exact superpose eq65061 eq64345
    | exact resolve eq64345 eq65061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64345 eq65061
  have eq67225 : ∀ X0 : G, x = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq66972 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66972
  have eq67534 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq553
       have i₂ := eq67225 sF0
       grind)
    | exact superpose eq67225 eq553
    | exact resolve eq553 eq67225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq67538 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq749
       have i₂ := eq67225 sF0
       grind)
    | exact superpose eq67225 eq749
    | exact resolve eq749 eq67225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749 eq67225
  have eq67587 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq67538
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq67538
    | exact resolve eq67538 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67538
  have eq67589 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq67534
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq67534
    | exact resolve eq67534 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67534
  have eq67666 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq67587
    | exact resolve eq67587 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67587
  have eq67820 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op x y) x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq67589 eq1160
    | exact resolve eq1160 eq67589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160 eq67589
  have eq67901 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq37617 eq67820
    | exact resolve eq67820 eq37617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37617 eq67820
  have eq67906 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq67901
    | exact resolve eq67901 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67901
  have eq69071 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq67906 eq67666
    | exact resolve eq67666 eq67906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67666 eq67906
  have eq69130 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq69071
  have eq69158 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq69130
       have r₂ := eq28
       grind)
    | exact resolve eq69130 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69130
  have eq69173 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq69158 eq30
    | exact resolve eq30 eq69158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq69158
  have eq69269 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq69173
    | exact resolve eq69173 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq69173
  have eq69270 : x = y := by grind
  clear eq69269
  have eq69281 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq69270
       grind)
    | exact superpose eq69270 eq19
    | exact resolve eq19 eq69270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq69282 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq69270
       grind)
    | exact superpose eq69270 eq25
    | exact resolve eq25 eq69270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq69270
  have eq69448 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq69282
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq69282
    | exact resolve eq69282 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq69282
  have eq69472 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq69448 eq27
    | exact resolve eq27 eq69448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq69448
  have eq69729 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq69472 eq87
    | exact resolve eq87 eq69472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87 eq69472
  have eq69814 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq69729
       have i₂ := eq69281
       grind)
    | exact superpose eq69281 eq69729
    | exact resolve eq69729 eq69281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69281 eq69729
  have eq69826 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq69814 eq15
    | exact resolve eq15 eq69814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69814
  have eq69874 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq69826
    | exact resolve eq69826 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq69826
  have eq69883 : False := by grind
  exact eq69883

/-- `Equation4554`: `x ◇ (y ◇ z) = (z ◇ w) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_pyx_pxy_Equation4554 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4554 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4554.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X3) X2) := by
    intro X0 X1 X2 X3
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
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
  have eq54 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X2 X5) X2) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X3 (M.op X2 x) X2 X5
       have i₂ := eq14 X0 X1 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op (M.op y X1) y) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X3 (M.op X4 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X0 X1 X2 x
       have i₂ := eq14 X3 X4 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x (M.op x x)
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq80
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq80
    | exact resolve eq80 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq83
    | exact resolve eq83 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq97 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq101 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq97
  have eq102 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq101
  have eq123 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq126 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq123
  have eq127 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq126
  have eq216 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op X2 (M.op x y)) := by
    intro X0 X2
    first
    | (have i₁ := eq55 X2 x
       have i₂ := eq55 X0 x
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 X1 X3 : G, (M.op X3 (M.op x y)) = (M.op X0 (M.op X1 y)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq55 X3 x
       have i₂ := eq14 X0 X1 y x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq216 eq127
    | exact resolve eq127 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq216
  have eq298 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq61 x x
       have i₂ := eq14 x x x X0
       grind)
    | exact superpose eq14 eq61
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op (M.op x y) x) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 X2 (M.op x x)
       have i₂ := eq61 X2 x
       grind)
    | exact superpose eq61 eq14
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : ∀ X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op (M.op x y) x) y) := by
    intro X1
    first
    | (have i₁ := eq55 X1 (M.op x x)
       have i₂ := eq61 y x
       grind)
    | exact superpose eq61 eq55
    | exact resolve eq55 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq306 : ∀ X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) x) (σ y)) := by
    intro X1
    first
    | (have i₁ := eq56 x (M.op X1 x)
       have i₂ := eq61 sF3 X1
       grind)
    | exact superpose eq61 eq56
    | exact resolve eq56 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq321 : ∀ X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    intro X1
    first
    | exact superpose eq62 eq56
    | exact resolve eq56 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq478 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 (M.op X1 y))) := by
    intro X0 X1
    first
    | exact superpose eq217 eq240
    | exact resolve eq240 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq493 : (σ (M.op (M.op x x) (M.op x x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq45
    | exact resolve eq45 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq514 : (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | exact superpose eq62 eq493
    | exact resolve eq493 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq493
  have eq515 : (M.op (M.op (σ x) (σ y)) (σ x)) = (σ (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq514
       have i₂ := eq61 (M.op x x) x
       grind)
    | exact superpose eq61 eq514
    | exact resolve eq514 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq711 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op (M.op x y) x) y)) := by
    first
    | exact superpose eq305 eq240
    | exact resolve eq240 eq305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq305
  have eq805 : ∀ X0 X1 X2 X3 : G, (M.op X1 (σ (M.op X0 X0))) = (M.op X2 (M.op X3 (σ X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X1 (σ X0) (σ X0) X2 X3
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq63
    | exact resolve eq63 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq929 : (M.op (M.op (M.op x y) x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq306 eq321
    | exact resolve eq321 eq306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306 eq321
  have eq965 : ∀ X0 X2 X3 X4 : G, (M.op X2 (M.op X3 (M.op X4 X0))) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq54 X3 X4 X0 X2 (M.op x x)
       have i₂ := eq61 X0 x
       grind)
    | exact superpose eq61 eq54
    | exact resolve eq54 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq3841 : (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op (M.op (M.op (M.op x y) x) y) (M.op (M.op (M.op x y) x) y))) := by
    first
    | exact superpose eq711 eq45
    | exact resolve eq45 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq3846 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq3841
       have i₂ := eq478 (M.op (M.op sF0 x) y) (M.op sF0 x)
       grind)
    | exact superpose eq478 eq3841
    | exact resolve eq3841 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3841
  have eq10959 : ∀ X0 X1 X2 : G, (M.op X0 (σ (M.op (M.op y y) (M.op y y)))) = (M.op X1 (M.op X2 (M.op (σ y) (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq805 (M.op y y) X0 X1 X2
       have i₂ := eq102
       grind)
    | exact superpose eq102 eq805
    | exact resolve eq805 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq805
  have eq11199 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op X1 (M.op X2 (M.op (σ y) (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10959 X0 X1 X2
       have i₂ := eq478 (M.op y y) y
       grind)
    | exact superpose eq478 eq10959
    | exact resolve eq10959 eq478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478 eq10959
  have eq52829 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op x y) x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3846
       have i₂ := eq302 (M.op sF1 sF1) sF1 sF1
       grind)
    | exact superpose eq302 eq3846
    | exact resolve eq3846 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3846
  have eq52915 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (M.op X1 (σ (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq302 eq52829
    | exact resolve eq52829 eq302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302 eq52829
  have eq62385 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq84 eq11
    | (have j0 := eq11 (σ x) (M.op (σ x) (σ x))
       grind)
    | exact resolve eq11 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq62393 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq62385
    | exact resolve eq62385 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62385
  have eq62398 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq62393
       have r₂ := eq28
       grind)
    | exact resolve eq62393 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62393
  have eq62402 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq62398 eq76
    | exact resolve eq76 eq62398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62398
  have eq62492 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq29 eq62402
    | exact resolve eq62402 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62402
  have eq62493 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq62492
  have eq62505 : (M.op x x) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq298 x
       have i₂ := eq62493
       grind)
    | exact superpose eq62493 eq298
    | exact resolve eq298 eq62493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq62508 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq61 X0 x
       have i₂ := eq62493
       grind)
    | exact superpose eq62493 eq61
    | exact resolve eq61 eq62493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq63034 : ∀ X0 : G, (M.op x x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq62505
       have i₂ := eq62508 sF0
       grind)
    | exact superpose eq62508 eq62505
    | exact resolve eq62505 eq62508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62505 eq62508
  have eq63229 : ∀ X0 : G, (M.op x x) = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq63034 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63034
  have eq65327 : ∀ X0 : G, x = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq62493
       have i₂ := eq63229 X0
       grind)
    | (have i₁ := eq62493
       have i₂ := eq63229 x
       grind)
    | exact superpose eq63229 eq62493
    | exact resolve eq62493 eq63229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62493 eq63229
  have eq65581 : ∀ X0 : G, x = (M.op X0 x) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq65327 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65327
  have eq65894 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq515
       have i₂ := eq65581 sF0
       grind)
    | exact superpose eq65581 eq515
    | exact resolve eq515 eq65581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq515
  have eq65898 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq711
       have i₂ := eq65581 sF0
       grind)
    | exact superpose eq65581 eq711
    | exact resolve eq711 eq65581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq65581
  have eq65937 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq65898
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq65898
    | exact resolve eq65898 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65898
  have eq65939 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq65894
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq65894
    | exact resolve eq65894 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65894
  have eq66020 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq65937
    | exact resolve eq65937 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65937
  have eq66046 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op x y) x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq65939 eq929
    | exact resolve eq929 eq65939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929 eq65939
  have eq66122 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op x y) x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq66046
    | exact resolve eq66046 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66046
  have eq66466 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq66020 eq52915
    | exact resolve eq52915 eq66020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66020
  have eq258528 : ∀ X0 : G, (M.op (M.op (M.op x y) x) (σ y)) = (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq11199 X0 x x
       have i₂ := eq965 sF3 x x sF3
       grind)
    | exact superpose eq965 eq11199
    | exact resolve eq11199 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965 eq11199
  have eq258529 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op x y) x) (σ y)) := by
    first
    | exact superpose eq52915 eq258528
    | exact resolve eq258528 eq52915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52915 eq258528
  have eq258537 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq66122 eq258529
    | exact resolve eq258529 eq66122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66122 eq258529
  have eq258792 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq258537 eq66466
    | exact resolve eq66466 eq258537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66466 eq258537
  have eq258916 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq258792
  have eq258974 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq258916
       have r₂ := eq28
       grind)
    | exact resolve eq258916 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258916
  have eq258995 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq258974 eq30
    | exact resolve eq30 eq258974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq258974
  have eq259091 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq258995
    | exact resolve eq258995 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq258995
  have eq259092 : x = y := by grind
  clear eq259091
  have eq259103 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq259092
       grind)
    | exact superpose eq259092 eq19
    | exact resolve eq19 eq259092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq259104 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq259092
       grind)
    | exact superpose eq259092 eq25
    | exact resolve eq25 eq259092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq259092
  have eq259292 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq259104
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq259104
    | exact resolve eq259104 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq259104
  have eq259322 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq259292 eq27
    | exact resolve eq27 eq259292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq259292
  have eq259653 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq259322 eq76
    | exact resolve eq76 eq259322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq259322
  have eq259811 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq259653
       have i₂ := eq259103
       grind)
    | exact superpose eq259103 eq259653
    | exact resolve eq259653 eq259103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259103 eq259653
  have eq259825 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq259811 eq15
    | exact resolve eq15 eq259811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259811
  have eq259902 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq259825
    | exact resolve eq259825 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq259825
  have eq259923 : False := by grind
  exact eq259923

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyx_pyy_pyx_pyy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq40 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
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
  have eq58 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq59 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq58 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq60 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq40 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq69 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq59 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq59 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq59 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq185 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq69 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq425 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq426 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq425 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq431 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq426 X0 X1
       have j1 := eq185 X0 X1
       grind)
    | (have r₁ := eq426 X0 X1
       have r₂ := eq185 X0 X1
       grind)
    | (have r₁ := eq426 X0 X0
       have r₂ := eq185 X0 X0
       grind)
    | exact resolve eq426 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq426
  have eq442 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq431 (σ X1) (σ X0)
       grind)
    | exact superpose eq431 eq15
    | exact resolve eq15 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq442 X0 X1
       have i₂ := eq431 X1 X0
       grind)
    | exact superpose eq431 eq442
    | exact resolve eq442 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431 eq442
  have eq449 : False := by grind
  exact eq449

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_pyy_pyx_pyy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = X1 := by
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
  clear eq19
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
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X0 X3
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq9 X2 X0 X2
       have i₂ := eq9 X0 X2 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq75 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X2 X2 X0 X3
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq63 X1 X2 X0 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq751 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq5076 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) X2) ∨ (σ X0) = (M.op X2 X2) ∨ (M.op (σ X0) (σ X1)) = (k X2 (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq751 X0 X0
       grind)
    | (have i₁ := eq13 X0 (σ X1)
       have i₂ := eq751 X0 X1
       grind)
    | exact superpose eq751 eq13
    | (have j0 := eq13 X2 (σ X0)
       have j1 := eq751 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq751 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq751 X0 X0
       grind)
    | exact resolve eq13 eq751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq6888 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0
       have i₂ := eq75 (τ X0) (τ X0) (τ X0) X1
       grind)
    | (have i₁ := eq70 X0
       have i₂ := eq75 (τ X0) X1 (τ X0) (τ X0)
       grind)
    | exact superpose eq75 eq70
    | exact resolve eq70 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq75
  have eq7097 : ∀ X0 X1 : G, (k X0 (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) = (τ (σ (M.op (M.op (τ (σ X0)) X1) (τ (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (σ (M.op (τ (σ X0)) (τ (σ X0))))
       have i₂ := eq6888 (σ X0) X1
       grind)
    | exact superpose eq6888 eq29
    | exact resolve eq29 eq6888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq6888
  have eq7113 : ∀ X0 X1 : G, (M.op (M.op (τ (σ X0)) X1) (τ (σ X0))) = (k X0 (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq7097 X0 X1
       have i₂ := eq10 (M.op (M.op (τ (σ X0)) X1) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq7097
    | exact resolve eq7097 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7097
  have eq7119 : ∀ X0 X1 : G, (k X0 (M.op (τ (σ X0)) (τ (σ X0)))) = (M.op (M.op (τ (σ X0)) X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7113 X0 X1
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq7113
    | exact resolve eq7113 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7113
  have eq7124 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7119 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7119
    | exact resolve eq7119 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7119
  have eq48713 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5076 X0 X1 (σ X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5076
  have eq48714 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq48713 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48713
  have eq48717 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq48714 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq48714
    | (have j0 := eq48714 X0 X1
       grind)
    | exact resolve eq48714 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48714
  have eq48718 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq48717 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48717
  have eq48760 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq48718 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq48718
    | (have j0 := eq48718 (τ X1) (τ X0)
       grind)
    | exact resolve eq48718 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq48831 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq48760 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48760
    | (have j0 := eq48760 X0 X1
       grind)
    | exact resolve eq48760 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48760
  have eq48856 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq48831 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq48831
    | (have j0 := eq48831 X0 X1
       grind)
    | exact resolve eq48831 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48831
  have eq48869 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq48856 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq48856
    | (have j0 := eq48856 X0 X1
       grind)
    | exact resolve eq48856 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48856
  have eq48878 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq48869 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq48869
    | (have j0 := eq48869 X0 X1
       grind)
    | exact resolve eq48869 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48869
  have eq48883 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48878 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq48878
    | (have j0 := eq48878 X0 X1
       grind)
    | exact resolve eq48878 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48878
  have eq48920 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq48718 X0 X1
       have i₂ := eq48883 X1 X0
       grind)
    | exact superpose eq48883 eq48718
    | (have j0 := eq48718 X0 X1
       have j1 := eq48883 (σ X1) (σ X0)
       grind)
    | exact resolve eq48718 eq48883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq405745 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq48920 x y
       grind)
    | exact superpose eq48920 eq16
    | (have j1 := eq48920 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq48920 x y
       grind)
    | exact resolve eq16 eq48920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48920
  have eq406248 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq405745
  have eq406614 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq7124 (σ y) (σ y)
       have i₂ := eq406248
       grind)
    | exact superpose eq406248 eq7124
    | exact resolve eq7124 eq406248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406248
  have eq406998 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq406614
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq406614
    | exact resolve eq406614 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406614
  have eq407206 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq48883 eq406998
    | (have j1 := eq48883 y x
       grind)
    | exact resolve eq406998 eq48883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48883 eq406998
  have eq407364 : x = (M.op y y) := by
    first
    | (have r₁ := eq407206
       have r₂ := eq16
       grind)
    | exact resolve eq407206 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407206
  have eq407583 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq7124 y y
       have i₂ := eq407364
       grind)
    | exact superpose eq407364 eq7124
    | exact resolve eq7124 eq407364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407364
  have eq409429 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq48718 x y
       have i₂ := eq407583
       grind)
    | exact superpose eq407583 eq48718
    | (have j0 := eq48718 x y
       grind)
    | exact resolve eq48718 eq407583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48718
  have eq409430 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq409429
       have r₂ := eq16
       grind)
    | exact resolve eq409429 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409429
  have eq409627 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq7124 (σ y) (σ y)
       have i₂ := eq409430
       grind)
    | exact superpose eq409430 eq7124
    | exact resolve eq7124 eq409430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7124 eq409430
  have eq410011 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq409627
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq409627
    | exact resolve eq409627 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409627
  have eq410218 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq410011
       have i₂ := eq407583
       grind)
    | exact superpose eq407583 eq410011
    | exact resolve eq410011 eq407583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq407583 eq410011
  have eq410376 : False := by grind
  exact eq410376

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_x_pyx_x_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = X1 := by
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
  clear eq19
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X0 X3
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq9 X2 X0 X2
       have i₂ := eq9 X0 X2 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  clear eq18
  have eq75 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X2 X2 X0 X3
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq63 X1 X2 X0 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1039 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq5894 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  have eq5895 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1039 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq1039
    | (have j0 := eq1039 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq1039 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6803 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X0
       have i₂ := eq75 (τ X0) (τ X0) (τ X0) X1
       grind)
    | (have i₁ := eq70 X0
       have i₂ := eq75 (τ X0) X1 (τ X0) (τ X0)
       grind)
    | exact superpose eq75 eq70
    | exact resolve eq70 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq75
  have eq7005 : ∀ X0 X1 : G, (k X0 (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) = (τ (σ (M.op (M.op (τ (σ X0)) X1) (τ (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 (σ (M.op (τ (σ X0)) (τ (σ X0))))
       have i₂ := eq6803 (σ X0) X1
       grind)
    | exact superpose eq6803 eq29
    | exact resolve eq29 eq6803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq6803
  have eq7019 : ∀ X0 X1 : G, (M.op (M.op (τ (σ X0)) X1) (τ (σ X0))) = (k X0 (τ (σ (M.op (τ (σ X0)) (τ (σ X0)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq7005 X0 X1
       have i₂ := eq10 (M.op (M.op (τ (σ X0)) X1) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq7005
    | exact resolve eq7005 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7005
  have eq7025 : ∀ X0 X1 : G, (k X0 (M.op (τ (σ X0)) (τ (σ X0)))) = (M.op (M.op (τ (σ X0)) X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7019 X0 X1
       have i₂ := eq10 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq10 eq7019
    | exact resolve eq7019 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7019
  have eq7030 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7025 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7025
    | exact resolve eq7025 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7025
  have eq44445 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5895 x y
       grind)
    | exact superpose eq5895 eq16
    | (have j1 := eq5895 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq5895 x y
       grind)
    | exact resolve eq16 eq5895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5895
  have eq44609 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq44445
  have eq385606 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44609
       grind)
    | exact superpose eq44609 eq16
    | exact resolve eq16 eq44609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385612 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq44609
       grind)
    | exact superpose eq44609 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq44609
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq44609
       grind)
    | exact resolve eq13 eq44609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44609
  have eq385874 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq385612
  have eq385875 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq385874
  have eq385877 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq385875
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq385875
    | exact resolve eq385875 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385875
  have eq385878 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14 eq385877
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq385877 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385877
  have eq385879 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq385878
       have r₂ := eq385606
       grind)
    | exact resolve eq385878 eq385606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385606 eq385878
  have eq386050 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq7030 (σ y) (σ y)
       have i₂ := eq385879
       grind)
    | exact superpose eq385879 eq7030
    | exact resolve eq7030 eq385879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385879
  have eq386433 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq386050
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq386050
    | exact resolve eq386050 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386050
  have eq386638 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq14 eq386433
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq386433 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386433
  have eq386797 : y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq386638
       have r₂ := eq16
       grind)
    | exact resolve eq386638 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386638
  have eq386854 : y ≠ y ∨ x = (M.op y y) ∨ y = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq386797
       grind)
    | exact superpose eq386797 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq386797
       grind)
    | exact resolve eq13 eq386797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq387116 : y ≠ y ∨ x = (M.op y y) ∨ y = (k y x) := by grind
  clear eq386854
  have eq387117 : y = (k y x) ∨ x = (M.op y y) := by grind
  clear eq387116
  have eq387119 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1039 y x
       have i₂ := eq387117
       grind)
    | exact superpose eq387117 eq1039
    | (have j0 := eq1039 y x
       grind)
    | exact resolve eq1039 eq387117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq387122 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq387119
  have eq523843 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq387122
       grind)
    | exact superpose eq387122 eq16
    | exact resolve eq16 eq387122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387122
  have eq524377 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq386797 eq523843
    | exact resolve eq523843 eq386797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523843
  have eq524378 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq524377
  have eq524595 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq7030 (σ y) (σ y)
       have i₂ := eq524378
       grind)
    | exact superpose eq524378 eq7030
    | exact resolve eq7030 eq524378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524378
  have eq525270 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq524595
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq524595
    | exact resolve eq524595 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524595
  have eq525516 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq387117 eq525270
    | exact resolve eq525270 eq387117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387117 eq525270
  have eq527321 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq525516
       grind)
    | exact superpose eq525516 eq16
    | exact resolve eq16 eq525516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525516
  have eq527854 : (σ y) ≠ (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq386797 eq527321
    | exact resolve eq527321 eq386797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386797 eq527321
  have eq527855 : x = (M.op y y) := by grind
  clear eq527854
  have eq527865 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq5894 y
       have i₂ := eq527855
       grind)
    | exact superpose eq527855 eq5894
    | exact resolve eq5894 eq527855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5894
  have eq528020 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq7030 y y
       have i₂ := eq527855
       grind)
    | exact superpose eq527855 eq7030
    | exact resolve eq7030 eq527855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527855
  have eq528327 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq527865
       have r₂ := eq16
       grind)
    | exact resolve eq527865 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527865
  have eq599797 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq528327
       grind)
    | exact superpose eq528327 eq16
    | exact resolve eq16 eq528327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq599803 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq528327
       grind)
    | exact superpose eq528327 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq528327
       grind)
    | exact resolve eq13 eq528327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528327
  have eq600138 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq599803
  have eq600139 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by grind
  clear eq600138
  have eq600145 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq600139
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq600139
    | exact resolve eq600139 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600139
  have eq600146 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq600145
       have i₂ := eq528020
       grind)
    | exact superpose eq528020 eq600145
    | exact resolve eq600145 eq528020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600145
  have eq600147 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq600146
       have r₂ := eq599797
       grind)
    | exact resolve eq600146 eq599797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599797 eq600146
  have eq600347 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq7030 (σ y) (σ y)
       have i₂ := eq600147
       grind)
    | exact superpose eq600147 eq7030
    | exact resolve eq7030 eq600147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7030 eq600147
  have eq600802 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq600347
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq600347
    | exact resolve eq600347 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600347
  have eq601026 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq600802
       have i₂ := eq528020
       grind)
    | exact superpose eq528020 eq600802
    | exact resolve eq600802 eq528020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528020 eq600802
  have eq601205 : False := by grind
  exact eq601205
