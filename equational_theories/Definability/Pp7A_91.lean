import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4494`: `x ◇ (y ◇ y) = (z ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,X) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_x_pyx_pxy_Equation4494 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4494 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4494.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) X1) := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
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
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq124 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq175 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X3 X1) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 x X1 X3
       have i₂ := eq16 x X1 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X1 X1)) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 (M.op x X1)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op X0 (M.op y y)) = (M.op (M.op x y) y) := by
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
  have eq180 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq16 X2 X1 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op X1 X1) (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) x
       have i₂ := eq16 (M.op x (M.op X1 X1)) X1 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : ∀ X1 : G, (M.op (M.op x y) y) = (M.op (M.op X1 y) y) := by
    intro X1
    first
    | (have i₁ := eq16 x y X1
       have i₂ := eq179 x
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op y y) (M.op y y))) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y y) x
       have i₂ := eq179 (M.op x (M.op y y))
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq190 X0
       have i₂ := eq179 (M.op y y)
       grind)
    | exact superpose eq179 eq190
    | exact resolve eq190 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq198 : ∀ X1 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op X1 (σ y)) (σ y)) := by
    intro X1
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y)))) := by
    intro X0
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) := by
    intro X0
    first
    | exact superpose eq180 eq202
    | exact resolve eq202 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq202
  have eq216 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq191 eq13
    | (have j0 := eq13 X0 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op x y) y)
       have r₂ := eq191 (M.op (M.op x y) y)
       grind)
    | exact resolve eq13 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq216 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq244 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq203 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq203 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact resolve eq13 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 : G, (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq244 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq427 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq219 eq34
    | exact resolve eq34 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq457 : ∀ X0 : G, (k X0 (σ (M.op (M.op x y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq427 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq427
    | exact resolve eq427 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq496 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X0 X2
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq11 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
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
  have eq519 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq531 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq532 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq531 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531
  have eq536 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq497 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq537 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op X1 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq496 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq546 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq536 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq536 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq536 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq536 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq558 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq731 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq761 : (σ (M.op (M.op x y) y)) ≠ (σ (M.op (M.op x y) y)) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq457 eq532
    | (have j0 := eq532 (σ (M.op (M.op x y) y))
       grind)
    | (have r₁ := eq532 (σ (M.op (M.op x y) y))
       have r₂ := eq457 (σ (M.op (M.op x y) y))
       grind)
    | exact resolve eq532 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq764 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq532 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq532
    | (have j0 := eq532 (σ X0)
       grind)
    | exact resolve eq532 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by grind
  clear eq761
  have eq777 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq546 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq546
    | (have j0 := eq546 (σ X0) X1
       grind)
    | exact resolve eq546 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq851 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq219 eq731
    | exact resolve eq731 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq852 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    intro X0
    first
    | exact superpose eq247 eq731
    | exact resolve eq731 eq247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq886 : ∀ X0 : G, (k X0 (τ (M.op (M.op (σ x) (σ y)) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq852 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq852
    | exact resolve eq852 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq887 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq851 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq851
    | exact resolve eq851 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq899 : (τ (M.op (M.op (σ x) (σ y)) (σ y))) ≠ (τ (M.op (M.op (σ x) (σ y)) (σ y))) ∨ (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (τ (M.op (M.op (σ x) (σ y)) (σ y))) (τ (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    first
    | exact superpose eq886 eq532
    | (have j0 := eq532 (τ (M.op (M.op (σ x) (σ y)) (σ y)))
       grind)
    | (have r₁ := eq532 (τ (M.op (M.op (σ x) (σ y)) (σ y)))
       have r₂ := eq886 (τ (M.op (M.op (σ x) (σ y)) (σ y)))
       grind)
    | exact resolve eq532 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq908 : (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op (τ (M.op (M.op (σ x) (σ y)) (σ y))) (τ (M.op (M.op (σ x) (σ y)) (σ y)))) := by grind
  clear eq899
  have eq926 : (τ (M.op (M.op x y) y)) ≠ (τ (M.op (M.op x y) y)) ∨ (τ (M.op (M.op x y) y)) = (M.op (τ (M.op (M.op x y) y)) (τ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq887 eq532
    | (have j0 := eq532 (τ (M.op (M.op x y) y))
       grind)
    | (have r₁ := eq532 (τ (M.op (M.op x y) y))
       have r₂ := eq887 (τ (M.op (M.op x y) y))
       grind)
    | exact resolve eq532 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq935 : (τ (M.op (M.op x y) y)) = (M.op (τ (M.op (M.op x y) y)) (τ (M.op (M.op x y) y))) := by grind
  clear eq926
  have eq1714 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (M.op X1 X1) (M.op X1 X1))) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (M.op X1 X1) x
       have i₂ := eq178 X0 X1 (M.op x (M.op X1 X1))
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1792 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) X1) = (M.op X3 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq182 X2 X1 X3
       have i₂ := eq181 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq182 X2 X1 X3
       have i₂ := eq181 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq181 eq182
    | exact resolve eq182 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1838 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (k X2 (M.op (M.op X1 X1) (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X1 X1) (M.op X1 X1))
       have i₂ := eq182 X0 X1 (M.op (M.op X1 X1) (M.op X1 X1))
       grind)
    | exact superpose eq182 eq13
    | (have j0 := eq13 X2 (M.op (M.op X1 X1) (M.op X1 X1))
       grind)
    | exact resolve eq13 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1849 : ∀ X1 X2 : G, (k X2 (M.op (M.op X1 X1) (M.op X1 X1))) = X2 := by
    intro X1 X2
    first
    | (have j0 := eq1838 x X1 X2
       grind)
    | (have r₁ := eq1838 X2 X1 X2
       have r₂ := eq16 (M.op X1 X1) X1 X2
       grind)
    | exact resolve eq1838 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1838
  have eq1896 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1849 X1 X2
       have i₂ := eq181 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq1849 X1 X2
       have i₂ := eq181 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq181 eq1849
    | exact resolve eq1849 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1898 : ∀ X0 X1 X2 : G, (k X2 (M.op (M.op X0 X1) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1849 (M.op X1 X1) X2
       have i₂ := eq182 X0 X1 (M.op (M.op X1 X1) (M.op X1 X1))
       grind)
    | exact superpose eq182 eq1849
    | exact resolve eq1849 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1849
  have eq1930 : ∀ X0 X1 X2 X3 : G, (k X2 (M.op X3 (M.op X0 (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1896 X3 (M.op X1 X1) X2
       have i₂ := eq181 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq1896 X3 (M.op X1 X1) X2
       have i₂ := eq181 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq181 eq1896
    | exact resolve eq1896 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1954 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op X2 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34 X0 (M.op X1 (M.op X2 X2))
       have i₂ := eq1896 X1 X2 (τ X0)
       grind)
    | exact superpose eq1896 eq34
    | exact resolve eq34 eq1896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1896
  have eq1970 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 X2)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1954 X0 X1 X2
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq1954
    | exact resolve eq1954 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1954
  have eq2013 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op X1 X2) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq731 X0 (M.op (M.op X1 X2) X2)
       have i₂ := eq1898 X1 X2 (σ X0)
       grind)
    | exact superpose eq1898 eq731
    | exact resolve eq731 eq1898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq2020 : ∀ X0 X1 : G, (τ (σ y)) = (k y (τ (M.op (M.op X0 X1) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq107 (M.op (M.op X0 X1) X1)
       have i₂ := eq1898 X0 X1 sF3
       grind)
    | exact superpose eq1898 eq107
    | exact resolve eq107 eq1898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq1898
  have eq2023 : ∀ X0 X1 : G, y = (k y (τ (M.op (M.op X0 X1) X1))) := by
    intro X0 X1
    first
    | exact superpose eq31 eq2020
    | exact resolve eq2020 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2020
  have eq2030 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op (M.op X1 X2) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2013 X0 X1 X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2013
    | exact resolve eq2013 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2013
  have eq2066 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq509
       grind)
    | exact superpose eq509 eq40
    | exact resolve eq40 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq2067 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2066
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2066
    | exact resolve eq2066 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2066
  have eq2069 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq2067
    | exact resolve eq2067 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2067
  have eq2239 : ∀ X0 X1 X2 X3 : G, (k X2 (σ (M.op X3 (M.op X0 (M.op X1 X1))))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1970 X2 X3 (M.op X1 X1)
       have i₂ := eq181 (M.op X1 X1) X1 X0
       grind)
    | (have i₁ := eq1970 X2 X3 (M.op X1 X1)
       have i₂ := eq181 X0 X1 (M.op X1 X1)
       grind)
    | exact superpose eq181 eq1970
    | exact resolve eq1970 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4513 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ X0)) (σ X0)) = (M.op X2 (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq537 (σ X0) X2 X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq537
    | (have j0 := eq537 (σ X0) X1 X2
       grind)
    | exact resolve eq537 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq41451 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (σ (M.op (M.op x y) y))))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq767 eq1930
    | exact resolve eq1930 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1930
  have eq41530 : ∀ X0 X1 : G, (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) = (M.op X0 (M.op X1 (σ (M.op (M.op x y) y)))) := by
    intro X0 X1
    first
    | exact superpose eq767 eq1792
    | exact resolve eq1792 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41623 : ∀ X0 X1 : G, (σ (M.op (M.op x y) y)) = (M.op X0 (M.op X1 (σ (M.op (M.op x y) y)))) := by
    intro X0 X1
    first
    | exact superpose eq767 eq41530
    | exact resolve eq41530 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767 eq41530
  have eq50901 : ∀ X0 : G, (M.op (τ (M.op (M.op (σ x) (σ y)) (σ y))) (τ (M.op (M.op (σ x) (σ y)) (σ y)))) = (M.op X0 (M.op (τ (M.op (M.op (σ x) (σ y)) (σ y))) (τ (M.op (M.op (σ x) (σ y)) (σ y))))) := by
    intro X0
    first
    | exact superpose eq908 eq182
    | exact resolve eq182 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51001 : ∀ X0 : G, (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (M.op X0 (τ (M.op (M.op (σ x) (σ y)) (σ y)))) := by
    intro X0
    first
    | exact superpose eq908 eq50901
    | exact resolve eq50901 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908 eq50901
  have eq56164 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 (τ (M.op (M.op x y) y))))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq935 eq1970
    | exact resolve eq1970 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1970
  have eq56178 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (M.op X2 (τ (M.op (M.op x y) y)))))) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq935 eq2239
    | exact resolve eq2239 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2239
  have eq56231 : ∀ X0 : G, (M.op (τ (M.op (M.op x y) y)) (τ (M.op (M.op x y) y))) = (M.op X0 (M.op (τ (M.op (M.op x y) y)) (τ (M.op (M.op x y) y)))) := by
    intro X0
    first
    | exact superpose eq935 eq182
    | exact resolve eq182 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56236 : ∀ X0 X1 : G, (M.op (τ (M.op (M.op x y) y)) (τ (M.op (M.op x y) y))) = (M.op X0 (M.op X1 (τ (M.op (M.op x y) y)))) := by
    intro X0 X1
    first
    | exact superpose eq935 eq1792
    | exact resolve eq1792 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56329 : ∀ X0 X1 : G, (τ (M.op (M.op x y) y)) = (M.op X0 (M.op X1 (τ (M.op (M.op x y) y)))) := by
    intro X0 X1
    first
    | exact superpose eq935 eq56236
    | exact resolve eq56236 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56236
  have eq56331 : ∀ X0 : G, (τ (M.op (M.op x y) y)) = (M.op X0 (τ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq935 eq56231
    | exact resolve eq56231 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935 eq56231
  have eq80058 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2069 eq519
    | exact resolve eq519 eq2069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80067 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq80058
       have r₂ := eq27
       grind)
    | exact resolve eq80058 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80058
  have eq81671 : ∀ X0 : G, (k X0 (τ (M.op (σ y) (σ y)))) = X0 ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq80067 eq2030
    | exact resolve eq2030 eq80067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2030
  have eq81768 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq80067 eq81671
    | exact resolve eq81671 eq80067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80067 eq81671
  have eq81797 : ∀ X0 : G, (k X0 y) = X0 ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq31 eq81768
    | exact resolve eq81768 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81768
  have eq81801 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (k X0 y) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq81797 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq81797 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq81797 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81797
  have eq81808 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op (M.op X1 (σ x)) (σ x)) ∨ (k X2 y) = X2 ∨ y = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq81801 (M.op X1 X1)
       grind)
    | exact superpose eq81801 eq16
    | (have j1 := eq81801 X2
       grind)
    | exact resolve eq16 eq81801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81812 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ (k X2 y) = X2 ∨ y = (M.op x x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X0 X1 X2
       have i₂ := eq81801 (M.op X1 X1)
       grind)
    | exact superpose eq81801 eq181
    | (have j1 := eq81801 X2
       grind)
    | exact resolve eq181 eq81801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81817 : ∀ X0 : G, (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 y) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq558 X0
       have i₂ := eq81801 (M.op X0 X0)
       grind)
    | exact superpose eq81801 eq558
    | (have j1 := eq81801 X0
       grind)
    | exact resolve eq558 eq81801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81940 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (σ y) (σ x)) ∨ (k X1 y) = X1 ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq81801 (M.op x X1)
       grind)
    | exact superpose eq81801 eq16
    | (have j1 := eq81801 X1
       grind)
    | exact resolve eq16 eq81801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81943 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (σ x)) = (M.op (σ y) (σ x)) ∨ (k X1 y) = X1 ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq175 X0 X1 x
       have i₂ := eq81801 (M.op x X1)
       grind)
    | exact superpose eq81801 eq175
    | (have j1 := eq81801 X1
       grind)
    | exact resolve eq175 eq81801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq83011 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (k X1 y) = X1 ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq26
       have i₂ := eq81812 X0 X1 (M.op sF2 sF3)
       grind)
    | exact superpose eq81812 eq26
    | (have j1 := eq81812 (σ x) X0 X1
       grind)
    | exact resolve eq26 eq81812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81812
  have eq83570 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op X1 (M.op X2 (M.op (σ x) (σ y)))) ∨ (k X3 y) = X3 ∨ y = (M.op x x) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1792 X0 X1 X2 X3
       have i₂ := eq83011 X0 (M.op X1 X1)
       grind)
    | exact superpose eq83011 eq1792
    | (have j1 := eq83011 X0 X3
       grind)
    | exact resolve eq1792 eq83011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1792
  have eq83936 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (k X1 y) = X1 ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq203 X0
       have i₂ := eq83011 X0 (M.op sF4 sF3)
       grind)
    | exact superpose eq83011 eq203
    | (have j1 := eq83011 X0 X1
       grind)
    | exact resolve eq203 eq83011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq84017 : ∀ X0 X1 : G, (τ (M.op (σ x) (σ y))) = (M.op X0 (τ (M.op (σ x) (σ y)))) ∨ (k X1 y) = X1 ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq51001 X0
       have i₂ := eq83011 X0 (M.op sF4 sF3)
       grind)
    | exact superpose eq83011 eq51001
    | (have j1 := eq83011 X0 X1
       grind)
    | exact resolve eq51001 eq83011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51001
  have eq84222 : ∀ X1 X2 X3 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op X1 (M.op X2 (M.op (σ x) (σ y)))) ∨ (k X3 y) = X3 ∨ y = (M.op x x) := by
    intro X1 X2 X3
    first
    | exact superpose eq198 eq83570
    | (have j0 := eq83570 (σ x) X1 X2 X3
       grind)
    | exact resolve eq83570 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83570
  have eq84311 : ∀ X1 X2 X3 : G, (M.op (σ y) (σ x)) = (M.op X1 (M.op X2 (M.op (σ x) (σ y)))) ∨ (k X3 y) = X3 ∨ y = (M.op x x) := by
    intro X1 X2 X3
    first
    | exact superpose eq81940 eq84222
    | (have j0 := eq84222 X1 X2 X3
       have j1 := eq81940 x X3
       grind)
    | exact resolve eq84222 eq81940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84222
  have eq84337 : ∀ X1 X3 : G, (M.op (σ y) (σ x)) = (M.op X1 (M.op (σ x) (σ y))) ∨ (k X3 y) = X3 ∨ y = (M.op x x) := by
    intro X1 X3
    first
    | exact superpose eq83936 eq84311
    | (have j0 := eq84311 X1 x X3
       have j1 := eq83936 x X3
       grind)
    | exact resolve eq84311 eq83936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84311
  have eq84344 : ∀ X3 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (k X3 y) = X3 ∨ y = (M.op x x) := by
    intro X3
    first
    | exact superpose eq83936 eq84337
    | (have j0 := eq84337 x X3
       have j1 := eq83936 x X3
       grind)
    | exact resolve eq84337 eq83936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83936 eq84337
  have eq128100 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (k (σ x) (M.op (σ x) (σ x))) (σ x)) ∨ (k X1 y) = X1 ∨ y = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq81808 X0 (M.op sF2 sF2) x
       have i₂ := eq558 sF2
       grind)
    | exact superpose eq558 eq81808
    | (have j0 := eq81808 X0 X1 X1
       have j1 := eq558 (σ x)
       grind)
    | exact resolve eq81808 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81808
  have eq128860 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (k (σ x) (σ y)) (σ x)) ∨ (k X1 y) = X1 ∨ y = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq81801 eq128100
    | (have j0 := eq128100 X0 X1
       have j1 := eq81801 X1
       grind)
    | exact resolve eq128100 eq81801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128100
  have eq128927 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (k (σ x) (σ y)) (σ x)) ∨ (k X1 y) = X1 ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq81801 eq128860
    | (have j0 := eq128860 X0 X1
       have j1 := eq81801 X1
       grind)
    | exact resolve eq128860 eq81801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128860
  have eq128958 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op (k (σ x) (σ y)) (σ x)) ∨ (k X1 y) = X1 ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq81940 eq128927
    | (have j0 := eq128927 X0 X1
       have j1 := eq81940 X0 X1
       grind)
    | exact resolve eq128927 eq81940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128927
  have eq128971 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (k (σ x) (σ y)) (σ x)) ∨ (k X1 y) = X1 ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X1
    first
    | exact superpose eq83011 eq128958
    | (have j0 := eq128958 (σ x) X1
       have j1 := eq83011 x X1
       grind)
    | exact resolve eq128958 eq83011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83011 eq128958
  have eq128976 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (k (σ x) (σ y)) (σ x)) ∨ (k X1 y) = X1 ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X1
    first
    | exact superpose eq84344 eq128971
    | (have j0 := eq128971 X1
       have j1 := eq84344 X1
       grind)
    | exact resolve eq128971 eq84344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128971
  have eq132032 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (k (σ x) (M.op (σ x) (σ x))) (σ x)) ∨ (k X0 y) = X0 ∨ y = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq81943 (M.op sF2 sF2) x
       have i₂ := eq558 sF2
       grind)
    | exact superpose eq558 eq81943
    | (have j0 := eq81943 X0 X0
       have j1 := eq558 (σ x)
       grind)
    | exact resolve eq81943 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81943
  have eq132314 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (k (σ x) (σ y)) (σ x)) ∨ (k X0 y) = X0 ∨ y = (M.op x x) ∨ (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq81801 eq132032
    | (have j0 := eq132032 X0
       have j1 := eq81801 X0
       grind)
    | exact resolve eq132032 eq81801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132032
  have eq132332 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op (k (σ x) (σ y)) (σ x)) ∨ (k X0 y) = X0 ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq81801 eq132314
    | (have j0 := eq132314 X0
       have j1 := eq81801 X0
       grind)
    | exact resolve eq132314 eq81801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81801 eq132314
  have eq132338 : ∀ X0 : G, (k (σ x) (σ y)) = (M.op (k (σ x) (σ y)) (σ x)) ∨ (k X0 y) = X0 ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq81817 eq132332
    | (have j0 := eq132332 X0
       have j1 := eq81817 X0
       grind)
    | exact resolve eq132332 eq81817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81817 eq132332
  have eq132340 : ∀ X0 : G, (k (σ x) (σ y)) = (M.op (k (σ x) (σ y)) (σ x)) ∨ (k X0 y) = X0 ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq81940 eq132338
    | (have j0 := eq132338 X0
       have j1 := eq81940 X0 X0
       grind)
    | exact resolve eq132338 eq81940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81940 eq132338
  have eq132342 : ∀ X0 : G, (k (σ x) (σ y)) = (M.op (k (σ x) (σ y)) (σ x)) ∨ (k X0 y) = X0 ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq84344 eq132340
    | (have j0 := eq132340 X0
       have j1 := eq84344 X0
       grind)
    | exact resolve eq132340 eq84344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84344 eq132340
  have eq132344 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (k X0 y) = X0 ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq128976 eq132342
    | (have j0 := eq132342 X0
       have j1 := eq128976 X0
       grind)
    | exact resolve eq132342 eq128976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128976 eq132342
  have eq132351 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) ∨ (k X0 y) = X0 ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2069
       have i₂ := eq132344 (k sF2 sF3)
       grind)
    | exact superpose eq132344 eq2069
    | (have j1 := eq132344 X0
       grind)
    | exact resolve eq2069 eq132344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2069 eq132344
  have eq132358 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) ∨ (k X0 y) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq132351 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132351
  have eq132362 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x x) ∨ (k X0 y) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq132358 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq132358 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq132358 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132358
  have eq132365 : ∀ X0 : G, y = (M.op x x) ∨ (k X0 y) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq132362 X0
       grind)
    | (have r₁ := eq132362 X0
       have r₂ := eq27
       grind)
    | exact resolve eq132362 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132362
  have eq138674 : ∀ X0 X2 : G, (τ (M.op (σ x) (σ y))) = (M.op X0 (M.op (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))))) ∨ (k X2 y) = X2 ∨ y = (M.op x x) := by
    intro X0 X2
    first
    | (have i₁ := eq84017 (M.op X0 (M.op (τ sF4) (τ sF4))) x
       have i₂ := eq1714 X0 (τ sF4) X2
       grind)
    | exact superpose eq1714 eq84017
    | (have j0 := eq84017 X0 X2
       grind)
    | exact resolve eq84017 eq1714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84017
  have eq138784 : ∀ X0 X2 : G, (τ (σ y)) = (M.op X0 (M.op (M.op (τ (σ y)) (τ (σ y))) (M.op (τ (σ y)) (τ (σ y))))) ∨ (k X2 y) = X2 ∨ y = (M.op x x) := by
    intro X0 X2
    first
    | exact superpose eq132365 eq138674
    | (have j0 := eq138674 X0 X2
       have j1 := eq132365 X2
       grind)
    | exact resolve eq138674 eq132365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132365 eq138674
  have eq139002 : ∀ X0 X2 : G, y = (M.op X0 (M.op (M.op y y) (M.op y y))) ∨ (k X2 y) = X2 ∨ y = (M.op x x) := by
    intro X0 X2
    first
    | exact superpose eq31 eq138784
    | (have j0 := eq138784 X0 X2
       grind)
    | exact resolve eq138784 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138784
  have eq139081 : ∀ X0 X2 : G, y = (M.op X0 (M.op (M.op x y) y)) ∨ (k X2 y) = X2 ∨ y = (M.op x x) := by
    intro X0 X2
    first
    | (have i₁ := eq139002 X0 X2
       have i₂ := eq179 (M.op y y)
       grind)
    | exact superpose eq179 eq139002
    | (have j0 := eq139002 X0 X2
       grind)
    | exact resolve eq139002 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq139002
  have eq139118 : ∀ X2 : G, y = (M.op (M.op x y) y) ∨ (k X2 y) = X2 ∨ y = (M.op x x) := by
    intro X2
    first
    | exact superpose eq191 eq139081
    | (have j0 := eq139081 x X2
       grind)
    | exact resolve eq139081 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139081
  have eq227617 : ∀ X0 : G, y = (M.op y y) ∨ (k X0 y) = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq186 x
       have i₂ := eq139118 (M.op x y)
       grind)
    | exact superpose eq139118 eq186
    | (have j1 := eq139118 X0
       grind)
    | exact resolve eq186 eq139118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq139118
  have eq227769 : ∀ X0 : G, y = (M.op x x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq227617 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq227617 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq227617 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227617
  have eq227863 : ∀ X0 X1 X2 : G, (M.op X0 y) = (M.op X1 y) ∨ (k X2 y) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X0 x X2
       have i₂ := eq227769 X0
       grind)
    | exact superpose eq227769 eq181
    | (have j1 := eq227769 X2
       grind)
    | exact resolve eq181 eq227769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227868 : ∀ X0 : G, (k x y) = (M.op y x) ∨ y = (M.op y y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq558 x
       have i₂ := eq227769 X0
       grind)
    | exact superpose eq227769 eq558
    | (have j1 := eq227769 X0
       grind)
    | exact resolve eq558 eq227769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq228008 : ∀ X0 X1 : G, (M.op X0 y) = (M.op y x) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x x
       have i₂ := eq227769 X0
       grind)
    | exact superpose eq227769 eq16
    | (have j1 := eq227769 X1
       grind)
    | exact resolve eq16 eq227769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227769
  have eq228201 : ∀ X0 : G, (k x y) = (M.op y x) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq227868 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq227868 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq227868 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227868
  have eq228800 : ∀ X0 X1 X2 X3 X4 : G, (k X1 (M.op X2 (M.op X3 (σ (M.op X0 y))))) = X1 ∨ (k X4 y) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq41451 X0 X1 X2
       have i₂ := eq227863 sF0 X1 X2
       grind)
    | (have i₁ := eq41451 X0 X1 X2
       have i₂ := eq227863 X0 sF0 X2
       grind)
    | exact superpose eq227863 eq41451
    | (have j1 := eq227863 X0 X1 X4
       grind)
    | exact resolve eq41451 eq227863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41451
  have eq228811 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 y)) = (M.op X1 (M.op X2 (σ (M.op X0 y)))) ∨ (k X3 y) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq41623 X0 X1
       have i₂ := eq227863 sF0 X1 X2
       grind)
    | (have i₁ := eq41623 X0 X1
       have i₂ := eq227863 X0 sF0 X2
       grind)
    | exact superpose eq227863 eq41623
    | (have j1 := eq227863 X0 X1 X3
       grind)
    | exact resolve eq41623 eq227863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41623
  have eq228818 : ∀ X0 X1 X2 X3 X4 : G, (k X1 (σ (M.op X2 (M.op X3 (τ (M.op X0 y)))))) = X1 ∨ (k X4 y) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56178 X0 X1 X2
       have i₂ := eq227863 sF0 X1 X2
       grind)
    | (have i₁ := eq56178 X0 X1 X2
       have i₂ := eq227863 X0 sF0 X2
       grind)
    | exact superpose eq227863 eq56178
    | (have j1 := eq227863 X0 X1 X4
       grind)
    | exact resolve eq56178 eq227863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56178
  have eq228825 : ∀ X0 X1 X2 X3 : G, (τ (M.op X0 y)) = (M.op X1 (M.op X2 (τ (M.op X0 y)))) ∨ (k X3 y) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56329 X0 X1
       have i₂ := eq227863 sF0 X1 X2
       grind)
    | (have i₁ := eq56329 X0 X1
       have i₂ := eq227863 X0 sF0 X2
       grind)
    | exact superpose eq227863 eq56329
    | (have j1 := eq227863 X0 X1 X3
       grind)
    | exact resolve eq56329 eq227863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56329
  have eq228993 : ∀ X0 X1 X2 : G, (k X1 y) = (M.op X0 y) ∨ (M.op X1 X1) = y ∨ y = (M.op y y) ∨ (k X2 y) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 X1 y
       have i₂ := eq227863 X1 X0 X2
       grind)
    | (have i₁ := eq11 X1 y
       have i₂ := eq227863 X0 X1 X2
       grind)
    | exact superpose eq227863 eq11
    | (have j0 := eq11 X1 y
       have j1 := eq227863 X0 X1 X2
       grind)
    | exact resolve eq11 eq227863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229264 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 y) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18
       have i₂ := eq227863 x X0 X1
       grind)
    | (have i₁ := eq18
       have i₂ := eq227863 X0 x X1
       grind)
    | exact superpose eq227863 eq18
    | (have j1 := eq227863 x X0 X1
       grind)
    | exact resolve eq18 eq227863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227863
  have eq229444 : ∀ X0 X1 X2 : G, (k X1 y) = (M.op X0 y) ∨ (M.op X1 X1) = y ∨ (k X2 y) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq228993 X0 X1 X2
       have j1 := eq13 X2 y
       grind)
    | (have r₁ := eq228993 X0 y X2
       have r₂ := eq13 X0 y
       grind)
    | (have r₁ := eq228993 X0 X1 X2
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq228993 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228993
  have eq229549 : ∀ X1 X2 X3 : G, (τ (M.op x y)) = (M.op X1 (M.op X2 (τ (M.op x y)))) ∨ (k X3 y) = X3 := by
    intro X1 X2 X3
    first
    | exact superpose eq229264 eq228825
    | (have j0 := eq228825 x X1 X2 X3
       have j1 := eq229264 x X3
       grind)
    | exact resolve eq228825 eq229264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228825
  have eq229556 : ∀ X1 X2 X3 X4 : G, (k X1 (σ (M.op X2 (M.op X3 (τ (M.op x y)))))) = X1 ∨ (k X4 y) = X4 := by
    intro X1 X2 X3 X4
    first
    | exact superpose eq229264 eq228818
    | (have j0 := eq228818 x X1 X2 X3 X4
       have j1 := eq229264 x X4
       grind)
    | exact resolve eq228818 eq229264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228818
  have eq229562 : ∀ X1 X2 X3 : G, (σ (M.op x y)) = (M.op X1 (M.op X2 (σ (M.op x y)))) ∨ (k X3 y) = X3 := by
    intro X1 X2 X3
    first
    | exact superpose eq229264 eq228811
    | (have j0 := eq228811 x X1 X2 X3
       have j1 := eq229264 x X3
       grind)
    | exact resolve eq228811 eq229264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228811
  have eq229573 : ∀ X1 X2 X3 X4 : G, (k X1 (M.op X2 (M.op X3 (σ (M.op x y))))) = X1 ∨ (k X4 y) = X4 := by
    intro X1 X2 X3 X4
    first
    | exact superpose eq229264 eq228800
    | (have j0 := eq228800 x X1 X2 X3 X4
       have j1 := eq229264 x X4
       grind)
    | exact resolve eq228800 eq229264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228800
  have eq229788 : ∀ X1 X2 : G, (M.op x y) = (k X1 y) ∨ (M.op X1 X1) = y ∨ (k X2 y) = X2 := by
    intro X1 X2
    first
    | exact superpose eq229264 eq229444
    | (have j0 := eq229444 x X1 X2
       have j1 := eq229264 x X2
       grind)
    | exact resolve eq229444 eq229264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229444
  have eq229806 : ∀ X1 X4 : G, (k X1 (σ (τ (M.op x y)))) = X1 ∨ (k X4 y) = X4 := by
    intro X1 X4
    first
    | exact superpose eq229549 eq229556
    | (have j0 := eq229556 X1 x x X4
       have j1 := eq229549 X1 x X4
       grind)
    | exact resolve eq229556 eq229549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229549 eq229556
  have eq229808 : ∀ X1 X2 X3 : G, (σ (M.op x y)) = (M.op X1 (M.op X2 (σ (M.op x y)))) ∨ (k X3 y) = X3 := by
    intro X1 X2 X3
    first
    | exact superpose eq20 eq229562
    | (have j0 := eq229562 X1 X2 X3
       grind)
    | exact resolve eq229562 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229562
  have eq229819 : ∀ X1 X2 X3 X4 : G, (k X1 (M.op X2 (M.op X3 (σ (M.op x y))))) = X1 ∨ (k X4 y) = X4 := by
    intro X1 X2 X3 X4
    first
    | exact superpose eq20 eq229573
    | (have j0 := eq229573 X1 X2 X3 X4
       grind)
    | exact resolve eq229573 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229573
  have eq229873 : ∀ X1 X4 : G, (k X4 y) = X4 ∨ (k X1 (M.op x y)) = X1 := by
    intro X1 X4
    first
    | (have i₁ := eq229806 X1 X4
       have i₂ := eq14 sF0
       grind)
    | exact superpose eq14 eq229806
    | (have j0 := eq229806 X1 X4
       grind)
    | exact resolve eq229806 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229806
  have eq229878 : ∀ X1 X4 : G, (k X4 y) = X4 ∨ (k X1 (σ (M.op x y))) = X1 := by
    intro X1 X4
    first
    | exact superpose eq229808 eq229819
    | (have j0 := eq229819 X1 x x X4
       have j1 := eq229808 X1 x X4
       grind)
    | exact resolve eq229819 eq229808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229808 eq229819
  have eq229984 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op x y) (M.op x y))) = (M.op (M.op X1 (M.op x y)) y) ∨ (k X2 y) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1714 X0 y X2
       have i₂ := eq229264 y X1
       grind)
    | (have i₁ := eq1714 X0 X1 X2
       have i₂ := eq229264 X0 (M.op X1 X1)
       grind)
    | exact superpose eq229264 eq1714
    | (have j1 := eq229264 X0 X2
       grind)
    | exact resolve eq1714 eq229264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1714
  have eq230388 : ∀ X0 X1 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq191 X0
       have i₂ := eq229264 sF0 X1
       grind)
    | (have i₁ := eq191 X0
       have i₂ := eq229264 X0 (M.op sF0 y)
       grind)
    | exact superpose eq229264 eq191
    | (have j1 := eq229264 X0 X1
       grind)
    | exact resolve eq191 eq229264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq229264
  have eq230764 : ∀ X0 X2 : G, (M.op X0 (M.op (M.op x y) (M.op x y))) = (M.op y x) ∨ (k X2 y) = X2 := by
    intro X0 X2
    first
    | exact superpose eq228008 eq229984
    | (have j0 := eq229984 X0 x X2
       have j1 := eq228008 X0 X2
       grind)
    | exact resolve eq229984 eq228008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228008 eq229984
  have eq230925 : ∀ X0 X2 : G, (k x y) = (M.op X0 (M.op (M.op x y) (M.op x y))) ∨ (k X2 y) = X2 := by
    intro X0 X2
    first
    | exact superpose eq228201 eq230764
    | (have j0 := eq230764 X0 X2
       have j1 := eq228201 X2
       grind)
    | exact resolve eq230764 eq228201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228201 eq230764
  have eq230983 : ∀ X0 X2 : G, (k x y) = (M.op X0 (M.op x y)) ∨ (k X2 y) = X2 := by
    intro X0 X2
    first
    | exact superpose eq230388 eq230925
    | (have j0 := eq230925 X0 X2
       have j1 := eq230388 X0 X2
       grind)
    | exact resolve eq230925 eq230388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230925
  have eq230998 : ∀ X2 : G, (M.op x y) = (k x y) ∨ (k X2 y) = X2 := by
    intro X2
    first
    | exact superpose eq230388 eq230983
    | (have j0 := eq230983 x X2
       have j1 := eq230388 x X2
       grind)
    | exact resolve eq230983 eq230388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230388 eq230983
  have eq231005 : ∀ X0 : G, y ≠ y ∨ y = (M.op y y) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq532 y
       have i₂ := eq229873 X0 y
       grind)
    | exact superpose eq229873 eq532
    | (have j0 := eq532 y
       have j1 := eq229873 X0 x
       grind)
    | (have r₁ := eq532 y
       have r₂ := eq229873 x y
       grind)
    | (have r₁ := eq532 (M.op x y)
       have r₂ := eq229873 (M.op x y) x
       grind)
    | exact resolve eq532 eq229873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229873
  have eq231076 : ∀ X0 : G, y = (M.op y y) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq231005 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231005
  have eq231166 : ∀ X0 : G, y ≠ y ∨ y = (M.op y y) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq532 y
       have i₂ := eq229878 X0 y
       grind)
    | exact superpose eq229878 eq532
    | (have j0 := eq532 y
       have j1 := eq229878 X0 x
       grind)
    | (have r₁ := eq532 y
       have r₂ := eq229878 x y
       grind)
    | (have r₁ := eq532 (σ (M.op x y))
       have r₂ := eq229878 (σ (M.op x y)) x
       grind)
    | exact resolve eq532 eq229878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229878
  have eq231237 : ∀ X0 : G, y = (M.op y y) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq231166 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231166
  have eq232897 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq40 x
       have i₂ := eq230998 X0
       grind)
    | (have i₁ := eq40 x
       have i₂ := eq230998 x
       grind)
    | exact superpose eq230998 eq40
    | (have j1 := eq230998 X0
       grind)
    | exact resolve eq40 eq230998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq230998
  have eq232900 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq232897 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq232897
    | (have j0 := eq232897 X0
       grind)
    | exact resolve eq232897 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq232897
  have eq232904 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq232900
    | (have j0 := eq232900 X0
       grind)
    | exact resolve eq232900 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232900
  have eq233084 : ∀ X0 X1 : G, (M.op y y) = (M.op X0 y) ∨ (k X1 (M.op x y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq231076 X0
       grind)
    | exact superpose eq231076 eq16
    | (have j1 := eq231076 X1
       grind)
    | exact resolve eq16 eq231076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233228 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ (k X1 (M.op x y)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq231076 eq233084
    | (have j0 := eq233084 X0 X1
       have j1 := eq231076 X1
       grind)
    | exact resolve eq233084 eq231076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231076 eq233084
  have eq237719 : ∀ X0 X1 : G, (M.op y y) = (M.op X0 y) ∨ (k X1 (σ (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq231237 X0
       grind)
    | exact superpose eq231237 eq16
    | (have j1 := eq231237 X1
       grind)
    | exact resolve eq16 eq231237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237863 : ∀ X0 X1 : G, y = (M.op X0 y) ∨ (k X1 (σ (M.op x y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq231237 eq237719
    | (have j0 := eq237719 X0 X1
       have j1 := eq231237 X1
       grind)
    | exact resolve eq237719 eq231237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231237 eq237719
  have eq238423 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq519
       have i₂ := eq232904 (k sF2 sF3)
       grind)
    | exact superpose eq232904 eq519
    | (have j1 := eq232904 X0
       grind)
    | exact resolve eq519 eq232904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519 eq232904
  have eq238437 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq238423 X0
       grind)
    | (have r₁ := eq238423 X0
       have r₂ := eq27
       grind)
    | exact resolve eq238423 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238423
  have eq238922 : ∀ X0 : G, (k X0 (M.op x y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq233228 x X0
       grind)
    | exact superpose eq233228 eq18
    | (have j1 := eq233228 x X0
       grind)
    | exact resolve eq18 eq233228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233228
  have eq239138 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq238922 eq777
    | (have j0 := eq777 (M.op x y) X0
       grind)
    | exact resolve eq777 eq238922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777 eq238922
  have eq239195 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq239138 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239138
  have eq239244 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq239195
    | (have j0 := eq239195 X0
       grind)
    | exact resolve eq239195 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239195
  have eq243671 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (τ y)))) = X0 ∨ (k X2 (σ (M.op x y))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56164 X0 X1
       have i₂ := eq237863 sF0 X1
       grind)
    | exact superpose eq237863 eq56164
    | (have j1 := eq237863 X0 X2
       grind)
    | exact resolve eq56164 eq237863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56164
  have eq243681 : ∀ X0 X1 : G, (τ y) = (M.op X0 (τ y)) ∨ (k X1 (σ (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq56331 X0
       have i₂ := eq237863 sF0 X1
       grind)
    | exact superpose eq237863 eq56331
    | (have j1 := eq237863 X0 X1
       grind)
    | exact resolve eq56331 eq237863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56331 eq237863
  have eq243685 : ∀ X0 X1 : G, (τ (M.op x y)) = (M.op X0 (τ (M.op x y))) ∨ (k X1 (σ (M.op x y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq239244 eq243681
    | (have j0 := eq243681 X0 X1
       have j1 := eq239244 X1
       grind)
    | exact resolve eq243681 eq239244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243681
  have eq243695 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op X1 (τ (M.op x y))))) = X0 ∨ (k X2 (σ (M.op x y))) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq239244 eq243671
    | (have j0 := eq243671 X0 X1 X2
       have j1 := eq239244 X2
       grind)
    | exact resolve eq243671 eq239244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239244 eq243671
  have eq243805 : ∀ X0 X2 : G, (k X0 (σ (τ (M.op x y)))) = X0 ∨ (k X2 (σ (M.op x y))) = X2 := by
    intro X0 X2
    first
    | exact superpose eq243685 eq243695
    | (have j0 := eq243695 X0 x X2
       have j1 := eq243685 X0 X2
       grind)
    | exact resolve eq243695 eq243685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243685 eq243695
  have eq243818 : ∀ X0 X2 : G, (k X2 (σ (M.op x y))) = X2 ∨ (k X0 (M.op x y)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq243805 X0 X2
       have i₂ := eq14 sF0
       grind)
    | exact superpose eq14 eq243805
    | (have j0 := eq243805 X0 X2
       grind)
    | exact resolve eq243805 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243805
  have eq245675 : ∀ X0 : G, (τ (σ (M.op x y))) = (k (M.op x y) (τ (σ (M.op x y)))) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq124 X0
       have i₂ := eq243818 (k sF1 X0) x
       grind)
    | exact superpose eq243818 eq124
    | (have j1 := eq243818 X0 x
       grind)
    | exact resolve eq124 eq243818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq243818
  have eq245697 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq245675
    | (have j0 := eq245675 (M.op x y)
       grind)
    | exact resolve eq245675 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq245675
  have eq245757 : ∀ X0 : G, (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq245697 X0
       have j1 := eq546 (M.op x y) X0
       grind)
    | (have r₁ := eq245697 X0
       have r₂ := eq546 (M.op x y) x
       grind)
    | (have r₁ := eq245697 (M.op x y)
       have r₂ := eq546 (M.op x y) x
       grind)
    | exact resolve eq245697 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245697
  have eq245797 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq245757 eq764
    | (have j0 := eq764 (M.op x y)
       grind)
    | exact resolve eq764 eq245757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245757
  have eq245856 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq245797
  have eq245905 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq245856
    | exact resolve eq245856 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245856
  have eq251494 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq245905 eq182
    | exact resolve eq182 eq245905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251631 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq245905 eq251494
    | exact resolve eq251494 eq245905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245905 eq251494
  have eq583634 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op x y))) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ (k X2 y) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4513 y X0 X1
       have i₂ := eq229788 y X2
       grind)
    | (have i₁ := eq4513 y X1 X2
       have i₂ := eq229788 X1 y
       grind)
    | exact superpose eq229788 eq4513
    | (have j0 := eq4513 y X1 X2
       have j1 := eq229788 y X2
       grind)
    | exact resolve eq4513 eq229788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4513 eq229788
  have eq583799 : ∀ X0 X1 X2 : G, (M.op X1 (σ (M.op x y))) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X2 y) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq583634 X0 X1 X2
       have j1 := eq13 X2 y
       grind)
    | (have r₁ := eq583634 X0 X1 X2
       have r₂ := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq583634 X0 X1 X2
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq583634 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583634
  have eq583854 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op X1 (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X2 y) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq583799 X0 X1 X2
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq583799
    | (have j0 := eq583799 X0 X1 X2
       grind)
    | exact resolve eq583799 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583799
  have eq583884 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op X1 (σ (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X2 y) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq20 eq583854
    | (have j0 := eq583854 X0 X1 X2
       grind)
    | exact resolve eq583854 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583854
  have eq583898 : ∀ X0 X2 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X2 y) = X2 := by
    intro X0 X2
    first
    | exact superpose eq251631 eq583884
    | (have j0 := eq583884 X0 x X2
       grind)
    | exact resolve eq583884 eq251631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251631 eq583884
  have eq583905 : ∀ X2 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X2 y) = X2 := by
    intro X2
    first
    | exact superpose eq198 eq583898
    | (have j0 := eq583898 (σ x) X2
       grind)
    | exact resolve eq583898 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq583898
  have eq583908 : ∀ X2 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k X2 y) = X2 := by
    intro X2
    first
    | (have i₁ := eq583905 X2
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq583905
    | (have j0 := eq583905 X2
       grind)
    | exact resolve eq583905 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583905
  have eq613794 : ∀ X0 : G, y = (k y (τ (M.op (σ y) (σ y)))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq2023 X0 x
       have i₂ := eq583908 (M.op X0 x)
       grind)
    | exact superpose eq583908 eq2023
    | (have j1 := eq583908 X0
       grind)
    | exact resolve eq2023 eq583908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613915 : ∀ X0 : G, y = (k y (τ (σ y))) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq583908 eq613794
    | (have j0 := eq613794 X0
       have j1 := eq583908 X0
       grind)
    | exact resolve eq613794 eq583908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583908 eq613794
  have eq613952 : ∀ X0 : G, y = (k y y) ∨ (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq31 eq613915
    | (have j0 := eq613915 y
       grind)
    | exact resolve eq613915 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613915
  have eq613954 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq613952 X0
       have j1 := eq546 y X0
       grind)
    | (have r₁ := eq613952 X0
       have r₂ := eq546 y x
       grind)
    | (have r₁ := eq613952 y
       have r₂ := eq546 y x
       grind)
    | exact resolve eq613952 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613952
  have eq659170 : ∀ X0 : G, y = (k y (τ (M.op (σ y) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq2023 X0 x
       have i₂ := eq238437 (M.op X0 x)
       grind)
    | exact superpose eq238437 eq2023
    | (have j1 := eq238437 X0
       grind)
    | exact resolve eq2023 eq238437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2023
  have eq659291 : ∀ X0 : G, y = (k y (τ (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq238437 eq659170
    | (have j0 := eq659170 X0
       have j1 := eq238437 X0
       grind)
    | exact resolve eq659170 eq238437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238437 eq659170
  have eq659329 : ∀ X0 : G, y = (k y y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq31 eq659291
    | (have j0 := eq659291 y
       grind)
    | exact resolve eq659291 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq659291
  have eq659331 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ x)) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq659329 X0
       have j1 := eq546 y X0
       grind)
    | (have r₁ := eq659329 X0
       have r₂ := eq546 y x
       grind)
    | (have r₁ := eq659329 y
       have r₂ := eq546 y x
       grind)
    | exact resolve eq659329 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq659329
  have eq659340 : ∀ X0 X1 X2 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ (k X2 y) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq181 X0 X1 X2
       have i₂ := eq659331 (M.op X1 X1)
       grind)
    | exact superpose eq659331 eq181
    | (have j1 := eq659331 X2
       grind)
    | exact resolve eq181 eq659331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq659331
  have eq661231 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (σ y)) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26
       have i₂ := eq659340 X0 X1 (M.op sF2 sF3)
       grind)
    | exact superpose eq659340 eq26
    | (have j1 := eq659340 (σ x) X0 X1
       grind)
    | exact resolve eq26 eq659340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659340
  have eq662865 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k X0 y) = X0 ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq613954 X0
       have i₂ := eq661231 X0 (M.op sF4 sF3)
       grind)
    | exact superpose eq661231 eq613954
    | (have j0 := eq613954 X0
       have j1 := eq661231 X0 X0
       grind)
    | exact resolve eq613954 eq661231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613954 eq661231
  have eq662874 : ∀ X0 X1 : G, (k X1 y) = X1 ∨ (k X0 y) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq662865 X1 X1
       grind)
    | (have r₁ := eq662865 X0 X1
       have r₂ := eq27
       grind)
    | exact resolve eq662865 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662865
  have eq664991 : ∀ X0 : G, X0 ≠ X0 ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq662874 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662874
  have eq664992 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq664991 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664991
  have eq665040 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq532 y
       have i₂ := eq664992 y
       grind)
    | exact superpose eq664992 eq532
    | (have j0 := eq532 y
       grind)
    | (have r₁ := eq532 y
       have r₂ := eq664992 y
       grind)
    | exact resolve eq532 eq664992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532
  have eq665044 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq764 y
       have i₂ := eq664992 y
       grind)
    | exact superpose eq664992 eq764
    | (have j0 := eq764 y
       grind)
    | exact resolve eq764 eq664992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764 eq664992
  have eq665146 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq665044
  have eq665148 : y = (M.op y y) := by grind
  clear eq665040
  have eq665216 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq665146
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq665146
    | exact resolve eq665146 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665146
  have eq665543 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y y
       have i₂ := eq665148
       grind)
    | exact superpose eq665148 eq16
    | exact resolve eq16 eq665148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665697 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq665543 X0
       have i₂ := eq665148
       grind)
    | exact superpose eq665148 eq665543
    | exact resolve eq665543 eq665148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665148 eq665543
  have eq666264 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq665216 eq182
    | exact resolve eq182 eq665216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq666409 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | exact superpose eq665216 eq666264
    | exact resolve eq666264 eq665216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665216 eq666264
  have eq667076 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq665697 x
       grind)
    | exact superpose eq665697 eq18
    | (have j1 := eq665697 x
       grind)
    | exact resolve eq18 eq665697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq665697
  have eq667311 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq667076
       grind)
    | exact superpose eq667076 eq24
    | exact resolve eq24 eq667076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq667076
  have eq667705 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq667311 eq20
    | exact resolve eq20 eq667311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq667311
  have eq669500 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq666409 eq26
    | (have j1 := eq666409 (σ x)
       grind)
    | exact resolve eq26 eq666409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq666409
  have eq669729 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq669500 eq27
    | exact resolve eq27 eq669500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq669500
  have eq669931 : False := by grind
  exact eq669931

/-- `Equation450`: `x = x ◇ (y ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pxx_pyx_Equation450 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law450 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law450.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X0)))) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq63 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X1
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq289 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq288 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq291 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq289 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq289 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq289 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq302 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq291 (σ X0)
       grind)
    | exact superpose eq291 eq15
    | exact resolve eq15 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq321 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq302 X0
       have i₂ := eq291 X0
       grind)
    | exact superpose eq291 eq302
    | exact resolve eq302 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291 eq302
  have eq366 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq63 (σ X0) (σ X0)
       have i₂ := eq321 X0
       grind)
    | exact superpose eq321 eq63
    | exact resolve eq63 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq321 X0
       grind)
    | exact superpose eq321 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq321 X0
       grind)
    | exact superpose eq321 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq368 X0 X1
       have j1 := eq369 X0 X1
       grind)
    | (have r₁ := eq368 X0 X1
       have r₂ := eq369 X0 X1
       grind)
    | exact resolve eq368 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq535 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq370 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq370
    | exact resolve eq370 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq370 X0 (σ X1)
       grind)
    | exact superpose eq370 eq15
    | (have j1 := eq370 X0 (σ X1)
       grind)
    | exact resolve eq15 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq616 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq535 X0 (τ X1)
       grind)
    | exact superpose eq535 eq17
    | (have j1 := eq535 X0 (τ X1)
       grind)
    | exact resolve eq17 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq535
  have eq723 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq616 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq616
    | exact resolve eq616 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq777 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq723 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq723
    | (have j0 := eq723 X0 X1
       grind)
    | exact resolve eq723 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq1630 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq546 x y
       grind)
    | exact superpose eq546 eq16
    | (have j1 := eq546 x y
       grind)
    | exact resolve eq16 eq546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq1708 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq1630
       have i₂ := eq777 y x
       grind)
    | exact superpose eq777 eq1630
    | (have j1 := eq777 (σ y) (σ x)
       grind)
    | (have r₁ := eq1630
       have r₂ := eq777 y x
       grind)
    | exact resolve eq1630 eq777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777 eq1630
  have eq1709 : x = (M.op y x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1708
  have eq1716 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq63 x y
       have i₂ := eq1709
       grind)
    | exact superpose eq1709 eq63
    | exact resolve eq63 eq1709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1709
  have eq1725 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq63 (σ x) (σ y)
       have i₂ := eq1716
       grind)
    | exact superpose eq1716 eq63
    | exact resolve eq63 eq1716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq1716
  have eq1728 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1725
       have i₂ := eq321 x
       grind)
    | exact superpose eq321 eq1725
    | exact resolve eq1725 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725
  have eq1735 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq366 x
       have i₂ := eq1728
       grind)
    | exact superpose eq1728 eq366
    | exact resolve eq366 eq1728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq1737 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq369 x X0
       have i₂ := eq1728
       grind)
    | exact superpose eq1728 eq369
    | (have j0 := eq369 x X0
       grind)
    | (have r₁ := eq369 x x
       have r₂ := eq1728
       grind)
    | exact resolve eq369 eq1728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1728
  have eq1750 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq1737 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737
  have eq1755 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq1750 X0
       have j1 := eq369 x X0
       grind)
    | (have r₁ := eq1750 X0
       have r₂ := eq369 x x
       grind)
    | exact resolve eq1750 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq1750
  have eq1756 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq1735
       have i₂ := eq321 x
       grind)
    | exact superpose eq321 eq1735
    | exact resolve eq1735 eq321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321 eq1735
  have eq1757 : (σ x) = (σ (M.op x x)) := by grind
  clear eq1756
  have eq1765 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq1757
       grind)
    | exact superpose eq1757 eq10
    | exact resolve eq10 eq1757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1757
  have eq1811 : x = (M.op x x) := by
    first
    | (have i₁ := eq1765
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1765
    | exact resolve eq1765 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1765
  have eq1817 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq12 X0 x
       have i₂ := eq1811
       grind)
    | exact superpose eq1811 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 X0 x
       have r₂ := eq1811
       grind)
    | exact resolve eq12 eq1811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811
  have eq1835 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq1817 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1817
  have eq1988 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq1755 (σ X0)
       grind)
    | exact superpose eq1755 eq15
    | exact resolve eq15 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755
  have eq2008 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1988 X0
       have i₂ := eq1835 X0
       grind)
    | exact superpose eq1835 eq1988
    | exact resolve eq1988 eq1835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835 eq1988
  have eq2089 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2008 y
       grind)
    | exact superpose eq2008 eq16
    | (have r₁ := eq16
       have r₂ := eq2008 y
       grind)
    | exact resolve eq16 eq2008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2008
  have eq2124 : False := by grind
  exact eq2124

/-- `Equation450`: `x = x ◇ (y ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_y_pxx_y_pyx_Equation450 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law450 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law450.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X0)))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
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
  have eq44 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 X1
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X1)
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq13
    | (have j0 := eq13 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X0)
       have r₂ := eq44 X0 X1
       grind)
    | exact resolve eq13 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq84 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq85 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
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
  clear eq18
  have eq251 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq16
    | (have j1 := eq84 x y
       grind)
    | exact resolve eq16 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 (σ X1) (σ X0)
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq44
    | (have j1 := eq84 X1 X0
       grind)
    | exact resolve eq44 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq260 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq84 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq832 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq85
    | exact resolve eq85 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq869 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq832 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq832
    | (have j0 := eq832 X0 X1
       grind)
    | exact resolve eq832 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq832
  have eq948 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq260 (M.op X0 X1) X1
       have i₂ := eq56 X0 X1
       grind)
    | exact superpose eq56 eq260
    | (have j0 := eq260 (M.op X0 X1) X1
       have j1 := eq56 X0 X1
       grind)
    | exact resolve eq260 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq959 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq948 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq1146 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq251
       have i₂ := eq869 y x
       grind)
    | exact superpose eq869 eq251
    | (have j1 := eq869 (σ y) (σ x)
       grind)
    | (have r₁ := eq251
       have r₂ := eq869 y x
       grind)
    | (have r₁ := eq251
       have r₂ := eq869 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq251
       have r₂ := eq869 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq251 eq869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq869
  have eq1147 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1146
  have eq1765 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq257 (τ X1) (τ X0)
       have i₂ := eq58 X0 X1
       grind)
    | exact superpose eq58 eq257
    | (have j0 := eq257 (τ X0) (τ X1)
       grind)
    | exact resolve eq257 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq257
  have eq1814 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ (k X0 X1))) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1765 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1765
    | (have j0 := eq1765 X0 X1
       grind)
    | exact resolve eq1765 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1765
  have eq1818 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1814 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1814
    | (have j0 := eq1814 X0 X1
       grind)
    | exact resolve eq1814 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814
  have eq1820 : ∀ X0 X1 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (k X0 X1) = (M.op (k X0 X1) X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1818 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1818
    | (have j0 := eq1818 X0 X1
       grind)
    | exact resolve eq1818 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1818
  have eq1821 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op (k X0 X1) X0) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1820 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1820
    | (have j0 := eq1820 X0 X1
       grind)
    | exact resolve eq1820 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1820
  have eq1822 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op (k X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1821 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1821
    | (have j0 := eq1821 X0 X1
       grind)
    | exact resolve eq1821 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1821
  have eq1823 : ∀ X0 X1 : G, (k X0 X1) = (M.op (k X0 X1) X0) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1822 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1822
    | (have j0 := eq1822 X0 X1
       grind)
    | exact resolve eq1822 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1822
  have eq14648 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ X0)) ∨ (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X0)
       have i₂ := eq959 X1 X0
       grind)
    | exact superpose eq959 eq10
    | (have j1 := eq959 X1 X0
       grind)
    | exact resolve eq10 eq959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959
  have eq14728 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14648 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq14648
    | (have j0 := eq14648 X0 X1
       grind)
    | exact resolve eq14648 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14648
  have eq14729 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ (M.op X1 X0)) (σ X0)) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14728 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14728
  have eq28668 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1147
       grind)
    | exact superpose eq1147 eq16
    | exact resolve eq16 eq1147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1147
  have eq28669 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq28668
       have r₂ := eq22 x
       grind)
    | exact resolve eq28668 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28668
  have eq28721 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14729 y x
       have i₂ := eq28669
       grind)
    | exact superpose eq28669 eq14729
    | exact resolve eq14729 eq28669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14729 eq28669
  have eq28724 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq28721
  have eq28888 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28724
       grind)
    | exact superpose eq28724 eq16
    | exact resolve eq16 eq28724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28724
  have eq28889 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq28888
       have r₂ := eq22 x
       grind)
    | exact resolve eq28888 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28888
  have eq28892 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28889
       grind)
    | exact superpose eq28889 eq16
    | exact resolve eq16 eq28889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28906 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq56 (σ x) (σ y)
       have i₂ := eq28889
       grind)
    | exact superpose eq28889 eq56
    | exact resolve eq56 eq28889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq28889
  have eq28971 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq28906
  have eq28996 : (σ x) = (σ y) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq28971
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq28971
    | exact resolve eq28971 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28971
  have eq29473 : y = (τ (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq28996
       grind)
    | exact superpose eq28996 eq10
    | exact resolve eq10 eq28996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28996
  have eq29593 : x = y ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq29473
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29473
    | exact resolve eq29473 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29473
  have eq29595 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29593
       grind)
    | exact superpose eq29593 eq16
    | exact resolve eq16 eq29593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29593
  have eq29596 : (σ x) = (σ (k y x)) := by
    first
    | (have r₁ := eq29595
       have r₂ := eq22 x
       grind)
    | exact resolve eq29595 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29595
  have eq29883 : (k y x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq29596
       grind)
    | exact superpose eq29596 eq10
    | exact resolve eq10 eq29596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29596
  have eq30005 : x = (k y x) := by
    first
    | (have i₁ := eq29883
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29883
    | exact resolve eq29883 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29883
  have eq30024 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq1823 y x
       have i₂ := eq30005
       grind)
    | exact superpose eq30005 eq1823
    | (have j0 := eq1823 y x
       grind)
    | exact resolve eq1823 eq30005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1823 eq30005
  have eq30029 : x = y ∨ x = (M.op x y) := by grind
  clear eq30024
  have eq30436 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30029
       grind)
    | exact superpose eq30029 eq16
    | exact resolve eq16 eq30029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30029
  have eq30441 : x = (M.op x y) := by
    first
    | (have r₁ := eq30436
       have r₂ := eq22 x
       grind)
    | exact resolve eq30436 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30436
  have eq30446 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq28892
       have i₂ := eq30441
       grind)
    | exact superpose eq30441 eq28892
    | exact resolve eq28892 eq30441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28892 eq30441
  have eq30502 : (σ x) = (σ y) := by grind
  clear eq30446
  have eq30909 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq30502
       grind)
    | exact superpose eq30502 eq10
    | exact resolve eq10 eq30502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30502
  have eq31029 : x = y := by
    first
    | (have i₁ := eq30909
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30909
    | exact resolve eq30909 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30909
  have eq31032 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
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
  have eq31038 : False := by grind
  exact eq31038

/-- `Equation4502`: `x ◇ (y ◇ y) = (z ◇ w) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_pyy_pyx_Equation4502 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4502 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4502.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X1) := by
    intro X0 X1 X2 X3
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
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
  have eq85 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq41 eq15
    | exact resolve eq15 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq44 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44
    | (have j0 := eq44 y
       grind)
    | exact resolve eq44 eq24
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
  have eq124 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq50
    | (have j0 := eq50 x
       grind)
    | exact resolve eq50 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144 : ∀ X0 : G, (k (k (M.op x y) X0) x) = (τ (k (k (σ (M.op x y)) (σ X0)) (σ x))) := by
    intro X0
    first
    | exact superpose eq37 eq59
    | exact resolve eq59 eq37
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
  have eq163 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq85 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq85
    | exact resolve eq85 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X4 X5) X2) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 x X2 X4 X5
       have i₂ := eq16 x X2 X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X3 (M.op (M.op X2 X2) (M.op X2 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op X2 X2) x x
       have i₂ := eq16 (M.op x x) X2 X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X3 (k (M.op X2 X2) (M.op X2 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq183 X0 X1 X2 X3
       have i₂ := eq174 (M.op X2 X2)
       grind)
    | exact superpose eq174 eq183
    | exact resolve eq183 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq186 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op X0 (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq181 X0 X1
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq181
    | exact resolve eq181 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq187 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op X0 (k X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq180 X0 X1
       have i₂ := eq174 X1
       grind)
    | exact superpose eq174 eq180
    | exact resolve eq180 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq190 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op X3 (k (k X2 X2) (k X2 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq184 X0 X1 X0 X3
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq184
    | exact resolve eq184 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq193 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (σ x) (σ y)) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq190 X0 X1 X2 x
       have i₂ := eq186 x (k X2 X2)
       grind)
    | exact superpose eq186 eq190
    | exact resolve eq190 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq194 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op (σ x) (σ y)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq193 X0 X1 X1
       have i₂ := eq186 sF4 X1
       grind)
    | exact superpose eq186 eq193
    | exact resolve eq193 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq195 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (M.op X2 X2) (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq174 (M.op X2 X2)
       have i₂ := eq16 (M.op X2 X2) X2 X0 X1
       grind)
    | exact superpose eq16 eq174
    | exact resolve eq174 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X2)) = (M.op (k X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 X2 X0 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq199 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op X2 (k (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 (M.op X2 x) X2 x
       have i₂ := eq174 (M.op X2 x)
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1 x
       have i₂ := eq186 x (M.op X0 X1)
       grind)
    | exact superpose eq186 eq199
    | exact resolve eq199 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq201 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) X2) = (M.op X1 (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq198 X0 X1 X2
       have i₂ := eq174 X2
       grind)
    | exact superpose eq174 eq198
    | exact resolve eq198 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq204 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (k (k X2 X2) (k X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq195 X0 X1 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq195
    | exact resolve eq195 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq205 : ∀ X0 X2 : G, (M.op (M.op (σ x) (σ y)) X2) = (M.op (k X0 X0) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq201 X0 x X2
       have i₂ := eq186 x X2
       grind)
    | exact superpose eq186 eq201
    | exact resolve eq201 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq207 : ∀ X2 : G, (k (k X2 X2) (k X2 X2)) = (M.op (M.op (σ x) (σ y)) X2) := by
    intro X2
    first
    | (have i₁ := eq204 x x X2
       have i₂ := eq194 x x X2
       grind)
    | (have i₁ := eq204 (σ x) (σ y) X2
       have i₂ := eq194 x x X2
       grind)
    | exact superpose eq194 eq204
    | (have j0 := eq204 (σ x) (σ y) X2
       grind)
    | exact resolve eq204 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq209 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (σ X0)) = (M.op X1 (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq186 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq186
    | exact resolve eq186 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq186 x X0
       have i₂ := eq187 x X0
       grind)
    | exact superpose eq187 eq186
    | exact resolve eq186 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq174 (k X0 X0)
       have i₂ := eq187 (k X0 X0) X0
       grind)
    | exact superpose eq187 eq174
    | exact resolve eq174 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (k X0 X0)) = (M.op X1 (M.op (M.op x y) X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 (k X0 X0) X2 X3
       have i₂ := eq187 (k X0 X0) X0
       grind)
    | exact superpose eq187 eq16
    | exact resolve eq16 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op X1 (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq227 X0 X1 x x
       have i₂ := eq186 (M.op x x) X0
       grind)
    | exact superpose eq186 eq227
    | exact resolve eq227 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186 eq227
  have eq234 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op X1 (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq225 eq231
    | exact resolve eq231 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq240 : (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op x y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq225 eq174
    | exact resolve eq174 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq278 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (σ (k X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq205 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq205
    | exact resolve eq205 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (σ (k X0 X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq225 eq278
    | exact resolve eq278 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq479 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq648 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (k (σ (τ X0)) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq293 (τ X0) X1
       have i₂ := eq38 X0 (τ X0)
       grind)
    | exact superpose eq38 eq293
    | exact resolve eq293 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 : G, (k (σ (k X0 X0)) (σ (k X0 X0))) = (M.op (M.op x y) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq174 (σ (k X0 X0))
       have i₂ := eq293 X0 (σ (k X0 X0))
       grind)
    | exact superpose eq293 eq174
    | exact resolve eq174 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq668 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ X0)) = (k (σ (k X0 X0)) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq658 X0
       have i₂ := eq209 X0 sF0
       grind)
    | exact superpose eq209 eq658
    | exact resolve eq658 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq658
  have eq673 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (k X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq648 X0 X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq648
    | exact resolve eq648 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq679 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ X0)) = (σ (k (k X0 X0) (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq668 X0
       have i₂ := eq10 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq10 eq668
    | exact resolve eq668 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq684 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ X0)) = (σ (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq679 X0
       have i₂ := eq207 X0
       grind)
    | exact superpose eq207 eq679
    | exact resolve eq679 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq679
  have eq686 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ X0)) = (σ (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq225 eq684
    | exact resolve eq684 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq688 : ∀ X0 : G, (M.op (M.op x y) (σ X0)) = (σ (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq225 eq686
    | exact resolve eq686 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq715 : (σ (k (M.op x y) (M.op x y))) = (M.op (M.op x y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq688 sF0
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq688
    | exact resolve eq688 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq720 : ∀ X0 : G, (M.op (M.op x y) X0) = (τ (M.op (M.op x y) (σ X0))) := by
    intro X0
    first
    | exact superpose eq688 eq15
    | exact resolve eq15 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq737 : (σ (k (M.op x y) (M.op x y))) = (M.op (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq715
    | exact resolve eq715 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq742 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq41 eq737
    | exact resolve eq737 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq737
  have eq745 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq742
    | exact resolve eq742 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq788 : ∀ X0 : G, (M.op (M.op x y) (τ X0)) = (τ (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq720 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq720
    | exact resolve eq720 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq798 : (M.op (M.op x y) x) = (τ (M.op (M.op x y) (σ x))) := by
    first
    | (have i₁ := eq720 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq720
    | (have j0 := eq720 x
       grind)
    | exact resolve eq720 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq799 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) (σ y))) := by
    first
    | (have i₁ := eq720 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq720
    | (have j0 := eq720 y
       grind)
    | exact resolve eq720 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720
  have eq871 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) X2) = (M.op (k X0 X1) X2) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq194 X1 X0 X2
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq194
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq194 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq876 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (k (k X0 X0) X1) ∨ (M.op (k X0 X0) X1) = X1 ∨ (k X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq187 X1 X0
       have i₂ := eq11 (k X0 X0) X1
       grind)
    | exact superpose eq11 eq187
    | (have j1 := eq11 (k X0 X0) X1
       grind)
    | exact resolve eq187 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq883 : (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq891 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq906 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = X1 ∨ (M.op (M.op x y) X0) = (k (k X0 X0) X1) ∨ (k X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq876 X0 X1
       have i₂ := eq205 X0 X1
       grind)
    | exact superpose eq205 eq876
    | (have j0 := eq876 X0 X1
       grind)
    | exact resolve eq876 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq876
  have eq911 : ∀ X0 X1 X2 : G, (M.op (M.op x y) X2) = (M.op (k X0 X1) X2) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq225 eq871
    | (have j0 := eq871 X0 X1 X2
       grind)
    | exact resolve eq871 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq929 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (k (k X0 X0) X1) ∨ (M.op (M.op x y) X1) = X1 ∨ (k X0 X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq225 eq906
    | (have j0 := eq906 X0 X1
       grind)
    | exact resolve eq906 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq974 : y ≠ (M.op x y) ∨ x = y ∨ (k x y) = (M.op y y) := by
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
  have eq977 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq983 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq977
       have i₂ := eq174 sF3
       grind)
    | exact superpose eq174 eq977
    | exact resolve eq977 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq986 : y ≠ (M.op x y) ∨ (k x y) = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq974
       have i₂ := eq174 y
       grind)
    | exact superpose eq174 eq974
    | exact resolve eq974 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq1057 : ∀ X0 X1 : G, (τ (M.op (M.op x y) X0)) = (M.op X1 (τ (M.op (M.op x y) X0))) := by
    intro X0 X1
    first
    | exact superpose eq788 eq234
    | exact resolve eq234 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1060 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (τ (M.op (M.op x y) X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq788 eq194
    | exact resolve eq194 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq1063 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (τ (M.op (M.op x y) X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq225 eq1060
    | exact resolve eq1060 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1060
  have eq1325 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op x y) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X1 X2 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq176
    | (have j0 := eq176 X0 X1 X2 x y
       grind)
    | exact resolve eq176 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq2827 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq883
       grind)
    | exact superpose eq883 eq39
    | exact resolve eq39 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2828 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq2827
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2827
    | exact resolve eq2827 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2827
  have eq2830 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq20 eq2828
    | exact resolve eq2828 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2828
  have eq2947 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq2830 eq891
    | exact resolve eq891 eq2830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq891
  have eq2957 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq2947
       have r₂ := eq27
       grind)
    | exact resolve eq2947 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2947
  have eq2964 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq2957 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq2957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2965 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq2957 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2957
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2957
       grind)
    | exact resolve eq12 eq2957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2971 : (k (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq2957 eq200
    | exact resolve eq200 eq2957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq2972 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2957 eq1325
    | exact resolve eq1325 eq2957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2973 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq2965
  have eq2974 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq2973
  have eq2975 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq2964
  have eq2977 : (k (σ x) (σ x)) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq225 eq2971
    | exact resolve eq2971 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2971
  have eq2983 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq2974
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq2974
    | exact resolve eq2974 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2974
  have eq2984 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq26 eq2975
    | exact resolve eq2975 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2975
  have eq2990 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq2830 eq2983
    | exact resolve eq2983 eq2830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2830 eq2983
  have eq2992 : (τ (σ (M.op x y))) = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq2990 eq97
    | exact resolve eq97 eq2990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2997 : ∀ X0 : G, (M.op (M.op x y) (σ x)) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2990 eq187
    | exact resolve eq187 eq2990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3002 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq2990 eq226
    | exact resolve eq226 eq2990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3014 : (k (σ x) (σ x)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq2977 eq3002
    | exact resolve eq3002 eq2977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3002
  have eq3018 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2977 eq2997
    | exact resolve eq2997 eq2977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2997
  have eq3022 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq28 eq2992
    | exact resolve eq2992 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2992
  have eq3024 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq2990 eq3014
    | exact resolve eq3014 eq2990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3014
  have eq3026 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2990 eq3018
    | exact resolve eq3018 eq2990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2990 eq3018
  have eq3041 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq226 x
       have i₂ := eq3022
       grind)
    | exact superpose eq3022 eq226
    | exact resolve eq226 eq3022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq3070 : (τ (σ (M.op x y))) = (k (τ (σ (M.op x y))) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq3024 eq163
    | exact resolve eq163 eq3024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq3093 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq28 eq3070
    | exact resolve eq3070 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3070
  have eq3122 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = X0 ∨ (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3026 eq12
    | (have j0 := eq12 (σ (M.op x y)) X0
       grind)
    | (have r₁ := eq12 X0 (σ (M.op x y))
       have r₂ := eq3026 X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3026 X0
       grind)
    | exact resolve eq12 eq3026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3026
  have eq3156 : ∀ X0 : G, (σ (M.op x y)) = X0 ∨ (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq3122 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3122
  have eq3167 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (k X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3156 X0
       have i₂ := eq174 sF1
       grind)
    | exact superpose eq174 eq3156
    | (have j0 := eq3156 X0
       grind)
    | exact resolve eq3156 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3156
  have eq3174 : ∀ X0 : G, (σ (M.op x y)) = (k X0 (σ (M.op x y))) ∨ (σ (M.op x y)) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3024 eq3167
    | (have j0 := eq3167 (k X0 (σ (M.op x y)))
       grind)
    | exact resolve eq3167 eq3024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3024 eq3167
  have eq3284 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq2972 eq26
    | (have j1 := eq2972 (σ y)
       grind)
    | exact resolve eq26 eq2972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2972
  have eq3323 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3284 eq234
    | exact resolve eq234 eq3284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq3360 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = X0 ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k X0 (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3323 eq12
    | (have j0 := eq12 (M.op (σ x) (σ y)) X0
       grind)
    | (have r₁ := eq12 X0 (M.op (σ x) (σ y))
       have r₂ := eq3323 X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq3323 X0
       grind)
    | exact resolve eq12 eq3323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3384 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq3323 eq240
    | exact resolve eq240 eq3323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3323
  have eq3395 : ∀ X0 : G, (M.op (σ x) (σ y)) = X0 ∨ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k X0 (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq3360 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3360
  have eq3400 : ∀ X0 : G, (M.op (M.op x y) (M.op (σ x) (σ y))) = (k X0 (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq225 eq3395
    | (have j0 := eq3395 X0
       grind)
    | exact resolve eq3395 eq225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225 eq3395
  have eq3407 : ∀ X0 : G, (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (k X0 (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq240 eq3400
    | (have j0 := eq3400 X0
       grind)
    | exact resolve eq3400 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3400
  have eq3410 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k X0 (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3384 eq3407
    | (have j0 := eq3407 (k X0 (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq3407 eq3384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3384 eq3407
  have eq3473 : (τ (k (σ x) (σ x))) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq2977 eq798
    | exact resolve eq798 eq2977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798 eq2977
  have eq3498 : (k x x) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq97 eq3473
    | exact resolve eq3473 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq3473
  have eq3504 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq3022 eq3498
    | exact resolve eq3498 eq3022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3022 eq3498
  have eq3513 : (σ (M.op x y)) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq3504 eq688
    | exact resolve eq688 eq3504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3504
  have eq3526 : (σ (M.op x y)) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq3513
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3513
    | exact resolve eq3513 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3513
  have eq3527 : (σ (M.op x y)) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq20 eq3526
    | exact resolve eq3526 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3526
  have eq4817 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq2984 eq152
    | exact resolve eq152 eq2984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2984
  have eq4823 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq29 eq4817
    | exact resolve eq4817 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4817
  have eq4981 : (σ (σ (M.op x y))) = (k (σ (M.op x y)) (σ (σ (M.op x y)))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq3174 eq37
    | (have j1 := eq3174 (M.op x y)
       grind)
    | exact resolve eq37 eq3174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3174
  have eq5115 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq3410 eq124
    | (have j1 := eq3410 (σ (M.op x y))
       grind)
    | exact resolve eq124 eq3410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq3410
  have eq5119 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq5115
       have r₂ := eq27
       grind)
    | exact resolve eq5115 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5115
  have eq15805 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq911 x y X0
       have i₂ := eq4823
       grind)
    | exact superpose eq4823 eq911
    | (have j0 := eq911 x y x
       grind)
    | exact resolve eq911 eq4823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4823
  have eq15952 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq15805 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15805
  have eq15961 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq15952 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15952
    | (have j0 := eq15952 X0
       grind)
    | exact resolve eq15952 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15952
  have eq15977 : ∀ X0 : G, (k (M.op x y) X0) = (M.op (M.op x y) (M.op x y)) ∨ (M.op (M.op x y) X0) = X0 ∨ (M.op x y) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3093 eq929
    | (have j0 := eq929 X0 X0
       grind)
    | exact resolve eq929 eq3093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq16101 : ∀ X0 : G, (k (M.op x y) X0) = (M.op (M.op x y) (M.op x y)) ∨ (M.op (M.op x y) X0) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq15977 X0
       have j1 := eq13 (M.op x y) X0
       grind)
    | (have r₁ := eq15977 X0
       have r₂ := eq13 (k (M.op x y) X0) (M.op (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq15977 X0
       have r₂ := eq13 (M.op (M.op x y) (M.op x y)) (k (M.op x y) X0)
       grind)
    | (have r₁ := eq15977 x
       have r₂ := eq13 (M.op (M.op x y) x) x
       grind)
    | exact resolve eq15977 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15977
  have eq16116 : ∀ X0 : G, (k (M.op x y) X0) = (k (M.op x y) (M.op x y)) ∨ (M.op (M.op x y) X0) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16101 X0
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq16101
    | (have j0 := eq16101 X0
       grind)
    | exact resolve eq16101 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16101
  have eq16122 : ∀ X0 : G, (M.op x y) = (k (M.op x y) X0) ∨ (M.op (M.op x y) X0) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq3093 eq16116
    | (have j0 := eq16116 X0
       grind)
    | exact resolve eq16116 eq3093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16116
  have eq16184 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) X0) ∨ (τ X0) = (M.op (M.op x y) (τ X0)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq16122 eq38
    | (have j1 := eq16122 (τ X0)
       grind)
    | exact resolve eq38 eq16122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq16122
  have eq16269 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) X0) ∨ (τ X0) = (M.op (M.op x y) (τ X0)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq20 eq16184
    | (have j0 := eq16184 X0
       grind)
    | exact resolve eq16184 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16184
  have eq16278 : ∀ X0 : G, (τ X0) = (τ (M.op (M.op x y) X0)) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq788 eq16269
    | (have j0 := eq16269 X0
       grind)
    | exact resolve eq16269 eq788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788 eq16269
  have eq16634 : ∀ X0 : G, (σ (τ X0)) = (M.op (M.op x y) X0) ∨ (σ (M.op x y)) = (k (σ (M.op x y)) X0) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq16278 eq14
    | (have j1 := eq16278 X0
       grind)
    | exact resolve eq14 eq16278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16278
  have eq16705 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) X0) ∨ (M.op (M.op x y) X0) = X0 ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16634 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq16634
    | (have j0 := eq16634 X0
       grind)
    | exact resolve eq16634 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16634
  have eq16869 : ∀ X0 : G, (τ (σ (M.op x y))) = (k (τ (σ (M.op x y))) X0) ∨ (σ X0) = (M.op (M.op x y) (σ X0)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq16705 eq479
    | (have j1 := eq16705 (σ X0)
       grind)
    | exact resolve eq479 eq16705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq16884 : (σ (σ (M.op x y))) = (k (σ (σ (M.op x y))) (σ x)) ∨ x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq16705 eq39
    | (have j1 := eq16705 x
       grind)
    | exact resolve eq39 eq16705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16895 : (τ (σ (M.op x y))) = (k (τ (σ (M.op x y))) y) ∨ (σ y) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq16705 eq152
    | (have j1 := eq16705 (σ y)
       grind)
    | exact resolve eq152 eq16705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq16705
  have eq16957 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq28 eq16895
    | exact resolve eq16895 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16895
  have eq16961 : (σ (σ (M.op x y))) = (k (σ (σ (M.op x y))) (σ x)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq3041 eq16884
    | exact resolve eq16884 eq3041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3041 eq16884
  have eq16966 : ∀ X0 : G, (σ X0) = (M.op (M.op x y) (σ X0)) ∨ (M.op x y) = (k (M.op x y) X0) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq28 eq16869
    | (have j0 := eq16869 X0
       grind)
    | exact resolve eq16869 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq16869
  have eq16974 : (σ (σ (M.op x y))) = (k (σ (σ (M.op x y))) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq3093 eq16961
    | exact resolve eq16961 eq3093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3093 eq16961
  have eq16991 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (τ (σ y)) X0) ∨ (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq16957 eq1063
    | exact resolve eq1063 eq16957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17003 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ y) X0) ∨ (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq16957 eq1325
    | exact resolve eq1325 eq16957
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16957
  have eq17018 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op y X0) ∨ (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq31 eq16991
    | exact resolve eq16991 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16991
  have eq17032 : (τ (σ (σ (M.op x y)))) = (k (τ (σ (σ (M.op x y)))) x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq16974 eq141
    | exact resolve eq141 eq16974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16974
  have eq17038 : (σ (M.op x y)) = (k (σ (M.op x y)) x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq17032
       have i₂ := eq15 sF1
       grind)
    | exact superpose eq15 eq17032
    | exact resolve eq17032 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17032
  have eq22085 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (τ (σ X0)) X1) ∨ (M.op x y) = (k (M.op x y) X0) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq16966 eq1063
    | (have j1 := eq16966 X0
       grind)
    | exact resolve eq1063 eq16966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063 eq16966
  have eq22148 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x y) X1) ∨ (M.op x y) = (k (M.op x y) X0) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq22085 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq22085
    | (have j0 := eq22085 X0 X1
       grind)
    | exact resolve eq22085 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22085
  have eq23573 : (σ x) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq17003 eq2957
    | exact resolve eq2957 eq17003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17003
  have eq23666 : (σ x) = (M.op (M.op x y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (k (M.op x y) y) := by grind
  clear eq23573
  have eq23719 : ∀ X0 : G, (τ (σ x)) = (M.op X0 (τ (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (k (M.op x y) y) := by
    intro X0
    first
    | exact superpose eq23666 eq1057
    | exact resolve eq1057 eq23666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057 eq23666
  have eq23758 : ∀ X0 : G, (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ x = (M.op X0 x) := by
    intro X0
    first
    | exact superpose eq29 eq23719
    | exact resolve eq23719 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23719
  have eq24295 : x ≠ (M.op (M.op x y) x) ∨ (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq17018
  have eq24366 : (M.op x y) = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have j1 := eq23758 y
       grind)
    | (have r₁ := eq24295
       have r₂ := eq23758 (M.op x y)
       grind)
    | exact resolve eq24295 eq23758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23758 eq24295
  have eq24377 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq24366 eq40
    | exact resolve eq40 eq24366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24389 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq20 eq24377
    | exact resolve eq24377 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24377
  have eq25434 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (k (M.op x y) X0) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq3527
       have i₂ := eq22148 sF0 sF2
       grind)
    | exact superpose eq22148 eq3527
    | (have j1 := eq22148 X0 x
       grind)
    | exact resolve eq3527 eq22148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3527 eq22148
  have eq25543 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (k (M.op x y) X0) := by
    intro X0
    first
    | (have j0 := eq25434 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25434
  have eq26174 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (M.op x y) = (k (M.op x y) (σ y)) := by
    first
    | exact superpose eq25543 eq2957
    | (have j1 := eq25543 (σ y)
       grind)
    | exact resolve eq2957 eq25543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2957 eq25543
  have eq26181 : (M.op x y) = (k (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq26174
  have eq26409 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26181 eq37
    | exact resolve eq37 eq26181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq26181
  have eq26418 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq26409
    | exact resolve eq26409 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26409
  have eq30826 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq15961 y
       grind)
    | (have i₁ := eq18
       have i₂ := eq15961 x
       grind)
    | exact superpose eq15961 eq18
    | (have j1 := eq15961 y
       grind)
    | exact resolve eq18 eq15961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15961
  have eq30997 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq30826 eq688
    | exact resolve eq688 eq30826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30826
  have eq31031 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq30997
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30997
    | exact resolve eq30997 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30997
  have eq31032 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq31031
    | exact resolve eq31031 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31031
  have eq31136 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq31032 eq3284
    | exact resolve eq3284 eq31032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31032
  have eq31174 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq31136
  have eq31201 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq31174
       have r₂ := eq27
       grind)
    | exact resolve eq31174 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31174
  have eq31211 : x = (k x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq31201
       grind)
    | exact superpose eq31201 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq31201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31220 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1325 y x X0
       have i₂ := eq31201
       grind)
    | exact superpose eq31201 eq1325
    | exact resolve eq1325 eq31201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31201
  have eq31223 : x = (k x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq31211
  have eq31234 : y = (M.op x y) ∨ x = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31223
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31223
    | exact resolve eq31223 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31223
  have eq31235 : x = (k x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq31234
  have eq31248 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq31235
       grind)
    | exact superpose eq31235 eq40
    | exact resolve eq40 eq31235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31235
  have eq31261 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31248
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31248
    | exact resolve eq31248 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31248
  have eq31280 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq31261 eq911
    | (have j0 := eq911 (σ x) (σ y) x
       grind)
    | exact resolve eq911 eq31261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911 eq31261
  have eq31284 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq31280 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31280
  have eq31287 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq31284
    | (have j0 := eq31284 X0
       grind)
    | exact resolve eq31284 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31284
  have eq31288 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq31287 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31287
  have eq31356 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq31220 y
       grind)
    | (have i₁ := eq18
       have i₂ := eq31220 x
       grind)
    | exact superpose eq31220 eq18
    | (have j1 := eq31220 y
       grind)
    | exact resolve eq18 eq31220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31220
  have eq31525 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31356 eq688
    | exact resolve eq688 eq31356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31356
  have eq31559 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31525
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31525
    | exact resolve eq31525 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31525
  have eq31560 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq31559
    | exact resolve eq31559 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31559
  have eq32781 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31288 eq26
    | (have j1 := eq31288 (σ y)
       grind)
    | exact resolve eq26 eq31288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31288
  have eq32949 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31560 eq32781
    | exact resolve eq32781 eq31560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31560 eq32781
  have eq32951 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq32949
       have r₂ := eq27
       grind)
    | exact resolve eq32949 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32949
  have eq32956 : (k (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32951 eq240
    | exact resolve eq240 eq32951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq32958 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32951 eq983
    | (have r₁ := eq983
       have r₂ := eq32951
       grind)
    | exact resolve eq983 eq32951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq983
  have eq32985 : (τ (σ y)) = (k (M.op x y) (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32951 eq5119
    | exact resolve eq5119 eq32951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5119
  have eq33054 : (τ (σ y)) = (k (M.op x y) (τ (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq32985
  have eq33082 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq32958
  have eq33083 : (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq33082
  have eq33095 : y = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq33054
    | exact resolve eq33054 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33054
  have eq33109 : (k (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq33083 eq32956
    | exact resolve eq32956 eq33083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32956
  have eq33116 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq24366 eq33095
    | exact resolve eq33095 eq24366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24366 eq33095
  have eq33117 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq33116
  have eq33124 : x = (k x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq33117
       grind)
    | exact superpose eq33117 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq33117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33133 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1325 y x X0
       have i₂ := eq33117
       grind)
    | exact superpose eq33117 eq1325
    | exact resolve eq1325 eq33117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33117
  have eq33136 : x = (k x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq33124
  have eq33147 : y = (M.op x y) ∨ x = (k x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33136
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq33136
    | exact resolve eq33136 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33136
  have eq33148 : x = (k x y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq33147
  have eq33161 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq33148
       grind)
    | exact superpose eq33148 eq40
    | exact resolve eq40 eq33148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33174 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq33161
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq33161
    | exact resolve eq33161 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33161
  have eq33446 : (k y y) = (τ (k (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq33083 eq115
    | exact resolve eq115 eq33083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq33465 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (k (σ x) (σ y)) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq33083 eq673
    | exact resolve eq673 eq33083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673 eq33083
  have eq33491 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq33174 eq33465
    | exact resolve eq33465 eq33174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33174 eq33465
  have eq33504 : (k x y) = (k y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq98 eq33446
    | exact resolve eq33446 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33446
  have eq33521 : (k x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq33504
       have r₂ := eq986
       grind)
    | exact resolve eq33504 eq986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq986 eq33504
  have eq33535 : (σ (k x y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq33521
       grind)
    | exact superpose eq33521 eq40
    | exact resolve eq40 eq33521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33521
  have eq33572 : (σ (k x y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq33535
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33535
    | exact resolve eq33535 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33535
  have eq33585 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq33572
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq33572
    | exact resolve eq33572 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq33572
  have eq33591 : (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq33585
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq33585
    | exact resolve eq33585 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33585
  have eq35200 : (τ (k (σ x) (σ y))) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq33109 eq799
    | exact resolve eq799 eq33109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799 eq33109
  have eq35277 : (k x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq98 eq35200
    | exact resolve eq35200 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq35200
  have eq35288 : x = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq33148 eq35277
    | exact resolve eq35277 eq33148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33148 eq35277
  have eq35302 : (σ x) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq35288 eq688
    | exact resolve eq688 eq35288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq35345 : (σ x) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq35302
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq35302
    | exact resolve eq35302 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35302
  have eq35351 : (σ x) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq35345
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35345
    | exact resolve eq35345 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35345
  have eq35861 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq33133 y
       grind)
    | (have i₁ := eq18
       have i₂ := eq33133 x
       grind)
    | exact superpose eq33133 eq18
    | (have j1 := eq33133 y
       grind)
    | exact resolve eq18 eq33133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33133
  have eq36047 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq35861 eq35288
    | exact resolve eq35288 eq35861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35288 eq35861
  have eq36077 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq36047
  have eq36098 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq36077 eq31
    | exact resolve eq31 eq36077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36077
  have eq36155 : x = y ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq36098
    | exact resolve eq36098 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36098
  have eq36156 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq36155
  have eq36164 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq883
       have i₂ := eq36156
       grind)
    | exact superpose eq36156 eq883
    | exact resolve eq883 eq36156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883 eq36156
  have eq36273 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq36164
  have eq40217 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq33491 eq26
    | (have j1 := eq33491 (σ y)
       grind)
    | exact resolve eq26 eq33491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33491
  have eq40403 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32951 eq40217
    | exact resolve eq40217 eq32951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32951 eq40217
  have eq40405 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq35351 eq40403
    | exact resolve eq40403 eq35351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35351 eq40403
  have eq40406 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq40405
  have eq40410 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq40406 eq31
    | exact resolve eq31 eq40406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40480 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq40410
    | exact resolve eq40410 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40410
  have eq40481 : y = (M.op x y) ∨ x = y := by grind
  clear eq40480
  have eq40821 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq40481
       grind)
    | exact superpose eq40481 eq18
    | exact resolve eq18 eq40481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40822 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq40481
       grind)
    | exact superpose eq40481 eq24
    | exact resolve eq24 eq40481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40879 : x ≠ (M.op x y) ∨ x = y := by grind
  have eq40899 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq40822
    | exact resolve eq40822 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40822
  have eq40941 : (k (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq40899 eq745
    | exact resolve eq745 eq40899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq41037 : (σ y) = (k (σ y) x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq40899 eq17038
    | exact resolve eq17038 eq40899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17038
  have eq41058 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq40899 eq24389
    | exact resolve eq24389 eq40899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24389
  have eq41096 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq41058
  have eq41117 : (σ y) = (k (σ y) x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq41037
  have eq41222 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq33591 eq41096
    | exact resolve eq41096 eq33591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41096
  have eq41243 : (σ y) = (k (σ y) x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq41117
       have r₂ := eq40879
       grind)
    | exact resolve eq41117 eq40879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41117
  have eq41360 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq40406 eq41222
    | exact resolve eq41222 eq40406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41222
  have eq41373 : (σ y) = (k (σ y) x) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq40406 eq41243
    | exact resolve eq41243 eq40406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41243
  have eq41465 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq40821 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq40821
       grind)
    | exact resolve eq12 eq40821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41475 : x = (M.op x y) ∨ (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq41465
  have eq41498 : (k x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have r₁ := eq41475
       have r₂ := eq40879
       grind)
    | exact resolve eq41475 eq40879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41475
  have eq41499 : (k x (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq41498
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq41498
    | exact resolve eq41498 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41498
  have eq41521 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq40941 eq3284
    | exact resolve eq3284 eq40941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3284
  have eq41575 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by grind
  clear eq41521
  have eq41606 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq33591 eq41575
    | exact resolve eq41575 eq33591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33591 eq41575
  have eq41617 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq40406 eq41606
    | exact resolve eq41606 eq40406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41606
  have eq41625 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq41360 eq41617
    | exact resolve eq41617 eq41360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41360 eq41617
  have eq41642 : (k (σ x) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq41499 eq35
    | exact resolve eq35 eq41499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq41499
  have eq41675 : (k (σ x) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq41 eq41642
    | exact resolve eq41642 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41642
  have eq41684 : (k (σ (M.op x y)) (σ (M.op x y))) = (k (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq20 eq41675
    | exact resolve eq41675 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41675
  have eq41691 : (k (σ y) (σ y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq40899 eq41684
    | exact resolve eq41684 eq40899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41684
  have eq41744 : ∀ X0 : G, (M.op (M.op x y) (σ y)) = (M.op X0 (k (σ x) (σ y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq41691 eq187
    | exact resolve eq187 eq41691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41782 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op X0 (k (σ x) (σ y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq40941 eq41744
    | exact resolve eq41744 eq40941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40941 eq41744
  have eq41795 : ∀ X0 : G, (k (σ x) (σ y)) = (M.op X0 (k (σ x) (σ y))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq41691 eq41782
    | exact resolve eq41782 eq41691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41782
  have eq44127 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq41625 eq1325
    | exact resolve eq1325 eq41625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41625
  have eq50364 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq36273 eq39
    | exact resolve eq39 eq36273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36273
  have eq50377 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | (have r₁ := eq50364
       have r₂ := eq40879
       grind)
    | exact resolve eq50364 eq40879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50364
  have eq50381 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq20 eq50377
    | exact resolve eq50377 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50377
  have eq50385 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq40899 eq50381
    | exact resolve eq50381 eq40899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50381
  have eq50416 : (τ (σ y)) = (k (τ (σ y)) x) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq50385 eq141
    | exact resolve eq141 eq50385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq50385
  have eq50434 : y = (k y x) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq31 eq50416
    | exact resolve eq50416 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50416
  have eq50438 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq40481 eq50434
    | exact resolve eq50434 eq40481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50434
  have eq51292 : (τ (k (σ (σ (M.op x y))) (σ x))) = (k (k (M.op x y) (σ (M.op x y))) x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq4981 eq144
    | exact resolve eq144 eq4981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4981
  have eq51297 : (τ (k (σ (M.op x y)) (σ x))) = (k (k (M.op x y) (σ y)) x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26418 eq144
    | exact resolve eq144 eq26418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq26418
  have eq51365 : (k (M.op x y) x) = (k (k (M.op x y) (σ y)) x) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq131 eq51297
    | exact resolve eq51297 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq51297
  have eq51369 : (k (σ (M.op x y)) x) = (k (k (M.op x y) (σ (M.op x y))) x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq59 eq51292
    | exact resolve eq51292 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq51292
  have eq51431 : (k (M.op x y) x) = (k (k (M.op x y) (σ y)) x) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq40406 eq51365
    | exact resolve eq51365 eq40406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51365
  have eq51435 : (k (σ (M.op x y)) x) = (k (k (M.op x y) (σ (M.op x y))) x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq40406 eq51369
    | exact resolve eq51369 eq40406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40406 eq51369
  have eq51474 : (M.op x y) = (k (k (M.op x y) (σ y)) x) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq50438 eq51431
    | exact resolve eq51431 eq50438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50438 eq51431
  have eq51478 : (k (σ y) x) = (k (k (M.op x y) (σ y)) x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq40899 eq51435
    | exact resolve eq51435 eq40899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51435
  have eq51505 : (M.op x y) = (k (k (M.op x y) (σ y)) x) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq40899 eq51474
    | exact resolve eq51474 eq40899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51474
  have eq51506 : (M.op x y) = (k (k (M.op x y) (σ y)) x) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) ∨ x = y := by grind
  clear eq51505
  have eq51512 : (σ y) = (k (k (M.op x y) (σ y)) x) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq41373 eq51478
    | exact resolve eq51478 eq41373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41373 eq51478
  have eq51524 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq51506 eq51512
    | exact resolve eq51512 eq51506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51506 eq51512
  have eq51529 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) x) ∨ x = y := by
    first
    | exact superpose eq40899 eq51524
    | exact resolve eq51524 eq40899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51524
  have eq51530 : x = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) ∨ x = y := by grind
  clear eq51529
  have eq51567 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq51530 eq1325
    | exact resolve eq1325 eq51530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325 eq51530
  have eq53269 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq40821
       have i₂ := eq51567 sF0
       grind)
    | exact superpose eq51567 eq40821
    | exact resolve eq40821 eq51567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51567
  have eq53434 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by grind
  clear eq53269
  have eq53510 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq53434
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq53434
    | exact resolve eq53434 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53434
  have eq53523 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq53510 eq41
    | exact resolve eq41 eq53510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq53553 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq20 eq53523
    | exact resolve eq53523 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53523
  have eq53563 : (σ y) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq40899 eq53553
    | exact resolve eq53553 eq40899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53553
  have eq53848 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq53563 eq41691
    | exact resolve eq41691 eq53563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41691 eq53563
  have eq53868 : (σ y) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by grind
  clear eq53848
  have eq53931 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq53868 eq41795
    | exact resolve eq41795 eq53868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41795 eq53868
  have eq53941 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | (have j0 := eq53931 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53931
  have eq54146 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq53941 eq26
    | (have j1 := eq53941 (σ x)
       grind)
    | exact resolve eq26 eq53941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53941
  have eq54313 : (σ (M.op x y)) ≠ (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq54146 eq27
    | exact resolve eq27 eq54146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54146
  have eq54449 : (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq54313
       have r₂ := eq40899
       grind)
    | exact resolve eq54313 eq40899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40899 eq54313
  have eq54451 : y = (τ (σ x)) ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq54449 eq31
    | exact resolve eq31 eq54449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54449
  have eq54559 : x = y ∨ x = y ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq29 eq54451
    | exact resolve eq54451 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54451
  have eq54560 : (M.op x y) = (σ y) ∨ x = y := by grind
  clear eq54559
  have eq54599 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq54560 eq26
    | exact resolve eq26 eq54560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54600 : y = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq54560 eq31
    | exact resolve eq31 eq54560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq54997 : (M.op x y) = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq40481 eq54600
    | exact resolve eq54600 eq40481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40481 eq54600
  have eq55307 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq54997 eq14
    | exact resolve eq14 eq54997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55393 : (M.op x y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq20 eq55307
    | exact resolve eq55307 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55307
  have eq66581 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq40821
       have i₂ := eq44127 sF0
       grind)
    | exact superpose eq44127 eq40821
    | exact resolve eq40821 eq44127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40821 eq44127
  have eq66770 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq66581
  have eq66858 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq66770
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq66770
    | exact resolve eq66770 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66770
  have eq66868 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq53510 eq66858
    | exact resolve eq66858 eq53510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53510 eq66858
  have eq66877 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54560 eq66868
    | exact resolve eq66868 eq54560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54560 eq66868
  have eq66897 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = y ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq66877 eq187
    | exact resolve eq187 eq66877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq66927 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (M.op X0 (M.op x y)) ∨ x = y ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq66897 X0
       have i₂ := eq174 sF0
       grind)
    | exact superpose eq174 eq66897
    | exact resolve eq66897 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66897
  have eq66941 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = y ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq66877 eq66927
    | exact resolve eq66927 eq66877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66877 eq66927
  have eq67132 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y ∨ (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq66941 eq54599
    | exact resolve eq54599 eq66941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54599 eq66941
  have eq67151 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (M.op x y) = (σ x) := by grind
  clear eq67132
  have eq67262 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y ∨ (M.op x y) = (σ x) := by
    first
    | exact superpose eq67151 eq27
    | exact resolve eq27 eq67151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67151
  have eq67436 : (M.op x y) = (σ x) ∨ x = y := by
    first
    | (have r₁ := eq67262
       have r₂ := eq55393
       grind)
    | exact resolve eq67262 eq55393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55393 eq67262
  have eq67455 : x = (τ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq67436 eq29
    | exact resolve eq29 eq67436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq67436
  have eq67803 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq54997 eq67455
    | exact resolve eq67455 eq54997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54997 eq67455
  have eq67859 : x = y := by
    first
    | (have r₁ := eq67803
       have r₂ := eq40879
       grind)
    | exact resolve eq67803 eq40879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40879 eq67803
  have eq67903 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq67859
       grind)
    | exact superpose eq67859 eq18
    | exact resolve eq18 eq67859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq67904 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq67859
       grind)
    | exact superpose eq67859 eq24
    | exact resolve eq24 eq67859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq67859
  have eq67910 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq67904
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq67904
    | exact resolve eq67904 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67904
  have eq67911 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq67903
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq67903
    | exact resolve eq67903 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67903
  have eq67913 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq67910 eq26
    | exact resolve eq26 eq67910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq67910
  have eq68000 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq67913
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq67913
    | exact resolve eq67913 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq67913
  have eq68020 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq67911
       grind)
    | exact superpose eq67911 eq39
    | exact resolve eq39 eq67911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq67911
  have eq68047 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq68020
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq68020
    | exact resolve eq68020 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq68020
  have eq68052 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq68000 eq68047
    | exact resolve eq68047 eq68000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68000 eq68047
  have eq68055 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq68052
    | exact resolve eq68052 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq68052
  have eq68057 : False := by grind
  exact eq68057

/-- `Equation4504`: `x ◇ (y ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_x_pxy_pyx_Equation4504 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4504 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4504.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  clear eq24
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
  have eq63 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op X0 (M.op X1 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | (have i₁ := eq14 X0 X1 X0 (M.op X1 X1)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 X1 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq78 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  clear eq75
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq98
    | exact resolve eq98 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
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
  have eq213 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq64 X0 (M.op x x)
       have i₂ := eq64 (M.op x x) x
       grind)
    | exact superpose eq64 eq64
    | exact resolve eq64 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq64 x x
       have i₂ := eq14 x x X0 X1
       grind)
    | (have i₁ := eq64 (M.op x (M.op X1 X1)) X1
       have i₂ := eq14 X0 X1 x (M.op X1 X1)
       grind)
    | exact superpose eq14 eq64
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq65 x x
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq65
    | exact resolve eq65 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq226 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (M.op x y) y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq224 eq14
    | exact resolve eq14 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) (σ y)) := by
    first
    | (have i₁ := eq226 x x
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq226
    | exact resolve eq226 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq359 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq213 eq13
    | (have j0 := eq13 X0 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op x y) y)
       have r₂ := eq213 (M.op (M.op x y) y)
       grind)
    | exact resolve eq13 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq359 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq368 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq363 eq34
    | exact resolve eq34 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 : G, (k X0 (σ (M.op (M.op x y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq368 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq368
    | exact resolve eq368 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq477 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq63 x x X2 X3 X5
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq63
    | exact resolve eq63 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq478 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X5) := by
    intro X5
    first
    | (have i₁ := eq477 x x X5
       have i₂ := eq64 x x
       grind)
    | exact superpose eq64 eq477
    | exact resolve eq477 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq688 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq78 X0 X0
       grind)
    | exact superpose eq78 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq78 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq78 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq13 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq78 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq696 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq695 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq698 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq688 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq706 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq698 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq698 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq698 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq1273 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq706 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq706
    | (have j0 := eq706 (τ X0) X1
       grind)
    | exact resolve eq706 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq706
  have eq1290 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1273 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1273
    | (have j0 := eq1273 X0 X1
       grind)
    | exact resolve eq1273 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273
  have eq1300 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1290 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1290
    | (have j0 := eq1290 X0 X1
       grind)
    | exact resolve eq1290 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1290
  have eq3648 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq696 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq696
    | (have j0 := eq696 (τ X0)
       grind)
    | exact resolve eq696 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq3665 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3648 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3648
    | (have j0 := eq3648 X0
       grind)
    | exact resolve eq3648 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3648
  have eq3675 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3665 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3665
    | (have j0 := eq3665 X0
       grind)
    | exact resolve eq3665 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3665
  have eq10655 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq10656 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq10655
    | exact resolve eq10655 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10655
  have eq10667 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq10656
       have r₂ := eq27
       grind)
    | exact resolve eq10656 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10656
  have eq10669 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq10667
    | exact resolve eq10667 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10667
  have eq10674 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq10669 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq10669
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq10669
       grind)
    | exact resolve eq13 eq10669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10669
  have eq10680 : ∀ X0 : G, x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq10674 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10674
  have eq10801 : ∀ X0 X1 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq10680 X1
       grind)
    | exact superpose eq10680 eq13
    | (have j0 := eq13 X0 x
       have j1 := eq10680 X1
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq10680 X0
       grind)
    | exact resolve eq13 eq10680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10680
  have eq10806 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq10801 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10801
  have eq10834 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq49
       have i₂ := eq10806 (k sF2 sF2) x
       grind)
    | exact superpose eq10806 eq49
    | (have j1 := eq10806 X0 x
       grind)
    | exact resolve eq49 eq10806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10806
  have eq10916 : ∀ X0 : G, x = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq10834
    | (have j0 := eq10834 x
       grind)
    | exact resolve eq10834 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10834
  have eq10942 : ∀ X0 : G, (k X0 x) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq10916 X0
       have j1 := eq1300 x X0
       grind)
    | (have r₁ := eq10916 X0
       have r₂ := eq1300 x x
       grind)
    | (have r₁ := eq10916 x
       have r₂ := eq1300 x x
       grind)
    | exact resolve eq10916 eq1300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300 eq10916
  have eq10983 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq696 x
       have i₂ := eq10942 x
       grind)
    | exact superpose eq10942 eq696
    | (have j0 := eq696 x
       grind)
    | exact resolve eq696 eq10942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696 eq10942
  have eq11005 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq10983
  have eq11024 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11005
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11005
    | exact resolve eq11005 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11005
  have eq11403 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq11024 eq64
    | exact resolve eq64 eq11024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13364 : (σ x) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11403 eq11024
    | exact resolve eq11024 eq11403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11024 eq11403
  have eq13367 : (σ x) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq13364
  have eq13388 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq13367 eq227
    | exact resolve eq227 eq13367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq13367
  have eq13425 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13388
    | exact resolve eq13388 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13388
  have eq13426 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13425
  have eq13428 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13426 eq224
    | exact resolve eq224 eq13426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq13431 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq13428
    | exact resolve eq13428 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13428
  have eq13436 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13431 eq213
    | exact resolve eq213 eq13431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq13439 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13431 eq363
    | exact resolve eq363 eq13431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363
  have eq13442 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13431 eq478
    | exact resolve eq478 eq13431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13431
  have eq13475 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13426 eq13436
    | exact resolve eq13436 eq13426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13436
  have eq13498 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq13475 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13475
  have eq13510 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13426 eq13439
    | exact resolve eq13439 eq13426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13439
  have eq13539 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq13510 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13510
  have eq13555 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13426 eq13442
    | exact resolve eq13442 eq13426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13426 eq13442
  have eq13586 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq13555 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13555
  have eq13595 : (σ x) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13498 (M.op x sF2)
       have i₂ := eq215 x sF2
       grind)
    | exact superpose eq215 eq13498
    | exact resolve eq13498 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13498
  have eq13664 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq13539 eq49
    | exact resolve eq49 eq13539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq13539
  have eq13748 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq13664
    | exact resolve eq13664 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq13664
  have eq13928 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq13748
       grind)
    | exact superpose eq13748 eq11
    | (have j0 := eq11 x x
       grind)
    | exact resolve eq11 eq13748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13748
  have eq13929 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq13928
  have eq14140 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq64 X0 x
       have i₂ := eq13929
       grind)
    | exact superpose eq13929 eq64
    | exact resolve eq64 eq13929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq21444 : ∀ X0 : G, (σ x) = (M.op X0 x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq14140 eq13595
    | exact resolve eq13595 eq14140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13595 eq14140
  have eq21469 : ∀ X0 : G, (σ x) = (M.op X0 x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21444 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21444
  have eq21759 : x = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13929
       have i₂ := eq21469 x
       grind)
    | exact superpose eq21469 eq13929
    | exact resolve eq13929 eq21469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13929 eq21469
  have eq21771 : x = (σ x) ∨ x = (M.op x y) := by grind
  clear eq21759
  have eq21873 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21771 eq13586
    | exact resolve eq13586 eq21771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13586 eq21771
  have eq21914 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq21873 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21873
  have eq23346 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq21914 y
       grind)
    | exact superpose eq21914 eq18
    | (have j1 := eq21914 y
       grind)
    | exact resolve eq18 eq21914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21914
  have eq23392 : x = (M.op x y) := by grind
  clear eq23346
  have eq23413 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq23392 eq20
    | exact resolve eq20 eq23392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23469 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq23392 eq369
    | exact resolve eq369 eq23392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq23471 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq23392 eq478
    | exact resolve eq478 eq23392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq23517 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq23471 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23471
    | (have j0 := eq23471 X0
       grind)
    | exact resolve eq23471 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23471
  have eq23519 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq23469 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23469
    | (have j0 := eq23469 X0
       grind)
    | exact resolve eq23469 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23469
  have eq23573 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq23413
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq23413
    | exact resolve eq23413 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq23413
  have eq23585 : ∀ X0 : G, x = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq23392 eq23517
    | exact resolve eq23517 eq23392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23517
  have eq23587 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq23519
    | (have j0 := eq23519 X0
       grind)
    | exact resolve eq23519 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq23519
  have eq23956 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq23573 eq26
    | exact resolve eq26 eq23573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq23573
  have eq24244 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq23587 eq3675
    | (have j0 := eq3675 (σ (M.op x y))
       grind)
    | (have r₁ := eq3675 (σ (M.op x y))
       have r₂ := eq23587 (σ (M.op x y))
       grind)
    | exact resolve eq3675 eq23587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3675 eq23587
  have eq24272 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq24244
  have eq25357 : (M.op (M.op x y) y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq24272 eq215
    | exact resolve eq215 eq24272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq25365 : (σ (M.op x y)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq24272 eq25357
    | exact resolve eq25357 eq24272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24272 eq25357
  have eq25371 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq23392 eq25365
    | exact resolve eq25365 eq23392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25365
  have eq25377 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq25371
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25371
    | exact resolve eq25371 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq25371
  have eq25383 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq23392 eq25377
    | exact resolve eq25377 eq23392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23392 eq25377
  have eq25458 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq25383 eq23956
    | exact resolve eq23956 eq25383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23956
  have eq25461 : x = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq25458
       have i₂ := eq23585 sF3
       grind)
    | exact superpose eq23585 eq25458
    | exact resolve eq25458 eq23585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23585 eq25458
  have eq25678 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq25461 eq27
    | exact resolve eq27 eq25461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq25461
  have eq25712 : False := by grind
  exact eq25712

/-- `Equation4504`: `x ◇ (y ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_x_pxx_pyx_Equation4504 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4504 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4504.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X3) X3) := by
    intro X0 X1 X2 X3
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
  clear eq35
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
  have eq178 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op X0 (M.op X1 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq16 X2 X3 (M.op x X5) X5
       have i₂ := eq16 X0 X1 x X5
       grind)
    | (have i₁ := eq16 X0 X1 X0 (M.op X1 X1)
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 X1 x y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X3 X3)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq178 x x X2 X3 X5
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq178
    | exact resolve eq178 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq185 : ∀ X5 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
    intro X5
    first
    | (have i₁ := eq184 x x X5
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq184
    | exact resolve eq184 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq190 : ∀ X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op x y) y) := by
    intro X2 X3
    first
    | (have i₁ := eq16 x x X2 X3
       have i₂ := eq179 x x
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq179 x x
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq179
    | exact resolve eq179 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq180
  have eq219 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq202 eq185
    | exact resolve eq185 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq185 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq185 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact resolve eq13 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq231 : ∀ X0 : G, (k X0 (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq227 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq234 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | exact superpose eq202 eq231
    | exact resolve eq231 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202 eq231
  have eq456 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq234 eq34
    | exact resolve eq34 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq484 : ∀ X0 : G, (k X0 (σ (M.op (M.op x y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq456 X0
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq456
    | exact resolve eq456 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456
  have eq578 : (M.op x y) = (k y x) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq634 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq759 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq234 eq673
    | exact resolve eq673 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq673
  have eq789 : ∀ X0 : G, (k X0 (τ (M.op (M.op x y) y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq759 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq759
    | exact resolve eq759 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq1552 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq634 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1903 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq578
       grind)
    | exact superpose eq578 eq39
    | exact resolve eq39 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq1904 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1903
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1903
    | exact resolve eq1903 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903
  have eq1906 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1904
    | exact resolve eq1904 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904
  have eq2060 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq1906 eq594
    | exact resolve eq594 eq1906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594 eq1906
  have eq2067 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq2060
       have r₂ := eq27
       grind)
    | exact resolve eq2060 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2060
  have eq2082 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq2067 eq190
    | exact resolve eq190 eq2067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2086 : (σ x) = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq2067 eq2082
    | exact resolve eq2082 eq2067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2067 eq2082
  have eq2146 : ∀ X0 : G, (k X0 (τ (σ x))) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq2086 eq789
    | exact resolve eq789 eq2086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789 eq2086
  have eq2198 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29 eq2146
    | exact resolve eq2146 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2146
  have eq2207 : ∀ X0 : G, (k X0 x) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq2198 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq2198 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq2198 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2198
  have eq2216 : x ≠ x ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1552 x
       have i₂ := eq2207 x
       grind)
    | exact superpose eq2207 eq1552
    | (have j0 := eq1552 x
       grind)
    | (have r₁ := eq1552 x
       have r₂ := eq2207 x
       grind)
    | exact resolve eq1552 eq2207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2207
  have eq2227 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2216
  have eq2252 : (M.op (M.op x y) y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq190 x x
       have i₂ := eq2227
       grind)
    | exact superpose eq2227 eq190
    | exact resolve eq190 eq2227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2256 : x = (M.op (M.op x y) y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2227 eq2252
    | exact resolve eq2252 eq2227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227 eq2252
  have eq2390 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2256 eq190
    | exact resolve eq190 eq2256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2256
  have eq2395 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2390
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2390
    | exact resolve eq2390 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2390
  have eq2429 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2395 eq31
    | exact resolve eq31 eq2395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2395
  have eq2460 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq2429
    | exact resolve eq2429 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2429
  have eq2461 : x = (M.op x y) ∨ x = y := by grind
  clear eq2460
  have eq2462 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq2461
       grind)
    | exact superpose eq2461 eq18
    | exact resolve eq18 eq2461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2463 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq22
       have i₂ := eq2461
       grind)
    | exact superpose eq2461 eq22
    | exact resolve eq22 eq2461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2461
  have eq2477 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq20 eq2463
    | exact resolve eq2463 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2463
  have eq2511 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2462 eq219
    | exact resolve eq219 eq2462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq2519 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq2462 eq484
    | exact resolve eq484 eq2462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq2583 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq20 eq2519
    | (have j0 := eq2519 X0
       grind)
    | exact resolve eq2519 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2519
  have eq2604 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq2477 eq2583
    | exact resolve eq2583 eq2477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2583
  have eq3062 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq2604 eq1552
    | (have j0 := eq1552 (σ x)
       grind)
    | (have r₁ := eq1552 (σ x)
       have r₂ := eq2604 (σ x)
       grind)
    | exact resolve eq1552 eq2604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1552 eq2604
  have eq3078 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq3062
  have eq3119 : (M.op (M.op x y) y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq3078 eq190
    | exact resolve eq190 eq3078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq3123 : (M.op x y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq2462 eq3119
    | exact resolve eq3119 eq2462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2462 eq3119
  have eq3148 : (M.op x y) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq3123 eq3078
    | exact resolve eq3078 eq3123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3078 eq3123
  have eq3165 : (M.op x y) = (σ x) ∨ x = y := by grind
  clear eq3148
  have eq3265 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq3165 eq26
    | exact resolve eq26 eq3165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3315 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2511 eq3265
    | exact resolve eq3265 eq2511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2511 eq3265
  have eq3332 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq3315 eq27
    | exact resolve eq27 eq3315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3315
  have eq3337 : (M.op x y) ≠ (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq2477 eq3332
    | exact resolve eq3332 eq2477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2477 eq3332
  have eq3338 : (M.op x y) ≠ (σ x) ∨ x = y := by grind
  clear eq3337
  have eq3339 : x = y := by
    first
    | (have r₁ := eq3338
       have r₂ := eq3165
       grind)
    | exact resolve eq3338 eq3165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3165 eq3338
  have eq3340 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3339
       grind)
    | exact superpose eq3339 eq18
    | exact resolve eq18 eq3339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq3341 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq3339
       grind)
    | exact superpose eq3339 eq24
    | exact resolve eq24 eq3339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3339
  have eq3392 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq3341
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3341
    | exact resolve eq3341 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3341
  have eq3394 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq3392 eq26
    | exact resolve eq26 eq3392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3392
  have eq3433 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq3340
       grind)
    | exact superpose eq3340 eq13
    | (have j0 := eq13 X0 x
       grind)
    | exact resolve eq13 eq3340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3439 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq634 x
       have i₂ := eq3340
       grind)
    | exact superpose eq3340 eq634
    | exact resolve eq634 eq3340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3340
  have eq3460 : ∀ X0 : G, (σ x) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq3394 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | exact resolve eq13 eq3394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3466 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3394 eq634
    | exact resolve eq634 eq3394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634 eq3394
  have eq4633 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq3439
       grind)
    | exact superpose eq3439 eq39
    | exact resolve eq39 eq3439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq3439
  have eq4638 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4633
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4633
    | exact resolve eq4633 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4633
  have eq4640 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq4638
    | exact resolve eq4638 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4638
  have eq4893 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4640 eq3466
    | exact resolve eq3466 eq4640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4906 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4893
       have r₂ := eq27
       grind)
    | exact resolve eq4893 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4893
  have eq4911 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4906 eq27
    | exact resolve eq27 eq4906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4918 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4906 eq3460
    | (have j0 := eq3460 X0
       grind)
    | (have r₁ := eq3460 X0
       have r₂ := eq4906
       grind)
    | exact resolve eq3460 eq4906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3460 eq4906
  have eq4924 : ∀ X0 : G, (k X0 (σ x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4918 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4918
  have eq5507 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4924 eq4640
    | exact resolve eq4640 eq4924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4640
  have eq5510 : (τ (σ x)) = (k x (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4924 eq90
    | exact resolve eq90 eq4924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq4924
  have eq5516 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq5507
  have eq5523 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq5510
    | exact resolve eq5510 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5510
  have eq5525 : x = (M.op x y) := by
    first
    | (have r₁ := eq5516
       have r₂ := eq4911
       grind)
    | exact resolve eq5516 eq4911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4911 eq5516
  have eq5538 : x = (k x x) := by
    first
    | (have j1 := eq3433 x
       grind)
    | (have r₁ := eq5523
       have r₂ := eq3433 x
       grind)
    | exact resolve eq5523 eq3433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3433 eq5523
  have eq5542 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq5538
       have i₂ := eq5525
       grind)
    | exact superpose eq5525 eq5538
    | exact resolve eq5538 eq5525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5538
  have eq5546 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq5525
       grind)
    | exact superpose eq5525 eq22
    | exact resolve eq22 eq5525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5525
  have eq5572 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5546 eq20
    | exact resolve eq20 eq5546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5546
  have eq5699 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5542 eq37
    | exact resolve eq37 eq5542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq5542
  have eq5706 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq5699
    | exact resolve eq5699 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5699
  have eq5707 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq5572 eq5706
    | exact resolve eq5706 eq5572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5706
  have eq5787 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5707 eq3466
    | exact resolve eq3466 eq5707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3466 eq5707
  have eq5795 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5787
  have eq5803 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq5795 eq27
    | exact resolve eq27 eq5795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq5795
  have eq5830 : False := by grind
  exact eq5830

/-- `Equation4513`: `x ◇ (y ◇ z) = (x ◇ y) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_y_x_pxx_pyx_Equation4513 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4513 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4513.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq59 : ∀ X0 : G, (k X0 x) = (τ (k (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
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
  have eq141 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq59 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq178 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X1) X4) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq16 X0 X1 x X4
       have i₂ := eq16 X0 X1 x X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 : G, (M.op x (M.op y X0)) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x y X0 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0 X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0 X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X2 x
       have i₂ := eq16 X0 X1 X3 x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X4)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq16 X0 X1 X4 (M.op X2 x)
       have i₂ := eq16 (M.op X0 X1) X2 x X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ X3 ∨ (M.op X0 X1) = (k (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X0 X1) X3
       have i₂ := eq16 X0 X1 X2 X3
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 (M.op X0 X1) X3
       grind)
    | (have r₁ := eq13 (M.op X0 X1) (M.op X0 (M.op X1 X2))
       have r₂ := eq16 X0 X1 X2 (M.op X0 (M.op X1 X2))
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 X2 : G, (M.op (M.op x y) X0) = (M.op (M.op x y) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq182 x X2
       have i₂ := eq182 x X0
       grind)
    | exact superpose eq182 eq182
    | exact resolve eq182 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 X3 : G, (M.op x (M.op y X0)) = (M.op (M.op (M.op x y) X1) X3) := by
    intro X0 X1 X3
    first
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq219 : ∀ X0 X1 : G, (M.op (M.op x y) X0) ≠ X1 ∨ (M.op x y) = (k (M.op x y) X1) := by
    intro X0 X1
    first
    | exact superpose eq189 eq13
    | (have j0 := eq13 (M.op x y) X1
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op (M.op x y) x)
       have r₂ := eq189 (M.op (M.op x y) x) x
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op (M.op x y) X0)
       have r₂ := eq189 X0 (M.op (M.op x y) X0)
       grind)
    | exact resolve eq13 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 X1 X3 : G, (M.op (M.op (σ x) (σ y)) X3) = (M.op (σ x) (M.op (M.op (σ y) X0) X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq183 (M.op X1 x) X1
       have i₂ := eq16 sF3 X1 x X3
       grind)
    | exact superpose eq16 eq183
    | exact resolve eq183 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq596 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have j0 := eq219 X0 (M.op (M.op x y) X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq602 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq596 eq37
    | exact resolve eq37 eq596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq596
  have eq603 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq20 eq602
    | (have j0 := eq602 X0
       grind)
    | exact resolve eq602 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq607 : ∀ X0 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x (M.op y X0)))) := by
    intro X0
    first
    | exact superpose eq182 eq603
    | exact resolve eq603 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq744 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq18
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq758 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq11 sF3 sF2
       grind)
    | exact superpose eq11 eq26
    | (have j1 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq772 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq773 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq772 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq777 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq11 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq11 X1 X1
       grind)
    | exact resolve eq12 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq785 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq777 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq788 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq785 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq785 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq785 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq785 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq789 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq773 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq773
    | (have j0 := eq773 (σ X0)
       grind)
    | exact resolve eq773 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq928 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq184 X0 x X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq184
    | (have j0 := eq184 X0 x y X1
       grind)
    | exact resolve eq184 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq934 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X1)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq184
    | (have j0 := eq184 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq184 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq1045 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op x y) X0)) = (M.op X1 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq928 X1 (M.op y x)
       have i₂ := eq182 x X0
       grind)
    | exact superpose eq182 eq928
    | exact resolve eq928 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq1048 : ∀ X0 X1 X2 : G, (M.op X2 (M.op x y)) = (M.op X2 (M.op (M.op x X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq928 X2 (M.op X0 x)
       have i₂ := eq16 x X0 x X1
       grind)
    | exact superpose eq16 eq928
    | exact resolve eq928 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1070 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op (M.op X0 x) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq16 X0 x x X2
       have i₂ := eq928 X0 x
       grind)
    | (have i₁ := eq16 X0 x y x
       have i₂ := eq928 X0 x
       grind)
    | exact superpose eq928 eq16
    | (have j0 := eq16 X0 x y X2
       grind)
    | exact resolve eq16 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1072 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) ≠ (M.op x X1) ∨ (k X0 (M.op x X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op x X1)
       have i₂ := eq928 X0 X1
       grind)
    | (have i₁ := eq13 X0 (M.op x y)
       have i₂ := eq928 X0 X1
       grind)
    | exact superpose eq928 eq13
    | (have j0 := eq13 X0 (M.op x X1)
       grind)
    | (have r₁ := eq13 x (M.op x (M.op x y))
       have r₂ := eq928 x (M.op x y)
       grind)
    | exact resolve eq13 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1110 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) = (M.op X1 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq183 eq934
    | exact resolve eq934 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1136 : ∀ X0 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ x)) X2) := by
    intro X0 X2
    first
    | exact superpose eq934 eq16
    | (have j0 := eq16 X0 (σ x) (σ y) X2
       grind)
    | exact resolve eq16 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1138 : ∀ X0 X1 : G, (M.op X0 (M.op (σ x) (σ y))) ≠ (M.op (σ x) X1) ∨ (k X0 (M.op (σ x) X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq934 eq13
    | (have j0 := eq13 X0 (M.op (σ x) X1)
       grind)
    | (have r₁ := eq13 (σ x) (M.op (σ x) (M.op (σ x) (σ y)))
       have r₂ := eq934 (σ x) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq13 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1207 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op (M.op X0 (M.op x y)) X2) := by
    intro X0 X2
    first
    | exact superpose eq1045 eq16
    | exact resolve eq16 eq1045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1045
  have eq1438 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 (M.op X1 X2)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1207 (M.op X0 X1) X2
       have i₂ := eq16 X0 X1 X2 sF0
       grind)
    | exact superpose eq16 eq1207
    | exact resolve eq1207 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1973 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ x) (σ y)) X3) = (M.op (σ x) (M.op (M.op (M.op (σ y) X0) X1) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq221 X0 (M.op X1 X2) X3
       have i₂ := eq16 (M.op sF3 X0) X1 X2 X3
       grind)
    | exact superpose eq16 eq221
    | exact resolve eq221 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq2886 : ∀ X0 X1 X2 X4 : G, (M.op X2 (M.op x y)) = (M.op X2 (M.op (M.op (M.op (M.op x y) X0) X1) X4)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq1048 (M.op y x) X4 X2
       have i₂ := eq200 x X0 X1
       grind)
    | exact superpose eq200 eq1048
    | exact resolve eq1048 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200 eq1048
  have eq5264 : ∀ X0 X1 X2 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x (M.op (M.op (M.op y X0) X1) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq607 (M.op X0 x)
       have i₂ := eq185 y X0 X1 X2 x
       grind)
    | exact superpose eq185 eq607
    | exact resolve eq607 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq607
  have eq19165 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq744
       grind)
    | exact superpose eq744 eq39
    | exact resolve eq39 eq744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq744
  have eq19166 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq19165
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19165
    | exact resolve eq19165 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq19165
  have eq19168 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq19166
    | exact resolve eq19166 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19166
  have eq29598 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq187 X0 X1 X2 (M.op X0 (M.op X1 X2))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq30002 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (k (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1110 eq29598
    | exact resolve eq29598 eq1110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq30062 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (k (M.op (M.op x y) X1) (M.op (M.op x y) X0)) := by
    intro X0 X1
    first
    | exact superpose eq189 eq29598
    | exact resolve eq29598 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq29598
  have eq52491 : x = (k x (M.op x (M.op x y))) := by
    first
    | (have j0 := eq1072 x (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq52495 : (σ x) = (k (σ x) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq52491 eq35
    | exact resolve eq35 eq52491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq52491
  have eq52499 : (σ x) = (k (σ x) (σ (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq52495
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq52495
    | exact resolve eq52495 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52495
  have eq52641 : (σ x) = (k (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | (have j0 := eq1138 (σ x) (M.op (σ x) (σ y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138
  have eq52645 : (τ (σ x)) = (k x (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq52641 eq90
    | exact resolve eq90 eq52641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq52641
  have eq52649 : x = (k x (τ (M.op (σ x) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq29 eq52645
    | exact resolve eq52645 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52645
  have eq62683 : ∀ X0 : G, (σ (M.op X0 (M.op (σ x) (σ y)))) ≠ (σ (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ (M.op X0 (M.op (σ x) (σ y)))) (σ (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq30002 eq789
    | (have j0 := eq789 (M.op X0 (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq789 eq30002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30002
  have eq62684 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) ≠ (σ (M.op (M.op x y) X0)) ∨ (σ (M.op (M.op x y) X0)) = (M.op (σ (M.op (M.op x y) X0)) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq30062 eq789
    | (have j0 := eq789 (M.op (M.op x y) X0)
       grind)
    | exact resolve eq789 eq30062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789 eq30062
  have eq62724 : ∀ X0 : G, (σ (M.op (M.op x y) X0)) = (M.op (σ (M.op (M.op x y) X0)) (σ (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have j0 := eq62684 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62684
  have eq62725 : ∀ X0 : G, (σ (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ (M.op X0 (M.op (σ x) (σ y)))) (σ (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have j0 := eq62683 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62683
  have eq63768 : ∀ X0 X1 X2 : G, (M.op (σ (M.op (M.op x y) X0)) X1) = (M.op (σ (M.op (M.op x y) X0)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq62724 eq178
    | exact resolve eq178 eq62724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64110 : ∀ X0 X1 : G, (σ (M.op (M.op x y) X0)) = (M.op (σ (M.op (M.op x y) X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq63768 eq62724
    | exact resolve eq62724 eq63768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62724 eq63768
  have eq64654 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 (M.op (σ x) (σ y)))) X1) = (M.op (σ (M.op X0 (M.op (σ x) (σ y)))) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq62725 eq178
    | exact resolve eq178 eq62725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65029 : ∀ X0 X1 : G, (σ (M.op X0 (M.op (σ x) (σ y)))) = (M.op (σ (M.op X0 (M.op (σ x) (σ y)))) X1) := by
    intro X0 X1
    first
    | exact superpose eq64654 eq62725
    | exact resolve eq62725 eq64654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62725 eq64654
  have eq65205 : ∀ X0 X1 : G, (σ (M.op X0 (M.op x y))) = (M.op (σ (M.op X0 (M.op x y))) X1) := by
    intro X0 X1
    first
    | exact superpose eq1207 eq65029
    | exact resolve eq65029 eq1207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65029
  have eq84653 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq19168 eq758
    | exact resolve eq758 eq19168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq758
  have eq84662 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq84653
       have r₂ := eq27
       grind)
    | exact resolve eq84653 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84653
  have eq85747 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq84662 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq84662
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq84662
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq84662
       grind)
    | exact resolve eq13 eq84662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84662
  have eq85795 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq85747
  have eq85823 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq19168 eq85795
    | exact resolve eq85795 eq19168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19168 eq85795
  have eq85871 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq85823 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq85823
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq85823
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq85823
       grind)
    | exact resolve eq13 eq85823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85823
  have eq85916 : (σ x) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq85871
  have eq85933 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq85916 eq141
    | exact resolve eq141 eq85916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq85916
  have eq85942 : x = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq29 eq85933
    | exact resolve eq85933 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85933
  have eq85947 : x = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq85942
       have r₂ := eq13 x x
       grind)
    | (have r₁ := eq85942
       have r₂ := eq13 y x
       grind)
    | exact resolve eq85942 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85942
  have eq85956 : x ≠ x ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq773 x
       have i₂ := eq85947
       grind)
    | exact superpose eq85947 eq773
    | (have j0 := eq773 x
       grind)
    | (have r₁ := eq773 x
       have r₂ := eq85947
       grind)
    | exact resolve eq773 eq85947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85947
  have eq85959 : x = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq85956
  have eq85992 : ∀ X0 : G, (M.op x X0) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq1070 y X0
       have i₂ := eq85959
       grind)
    | exact superpose eq85959 eq1070
    | exact resolve eq1070 eq85959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85999 : ∀ X0 X1 : G, (M.op x X1) = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq178 y x x x
       have i₂ := eq85959
       grind)
    | exact superpose eq85959 eq178
    | exact resolve eq178 eq85959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq86025 : ∀ X0 X1 : G, (M.op X0 x) = (M.op (M.op X0 x) X1) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq1438 X0 y x x
       have i₂ := eq85959
       grind)
    | exact superpose eq85959 eq1438
    | exact resolve eq1438 eq85959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1438
  have eq86053 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq86025 X0 x
       have i₂ := eq1070 X0 x
       grind)
    | exact superpose eq1070 eq86025
    | exact resolve eq86025 eq1070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070 eq86025
  have eq87869 : ∀ X0 : G, (M.op x y) = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq18
       have i₂ := eq85999 X0 y
       grind)
    | (have i₁ := eq18
       have i₂ := eq85999 y X0
       grind)
    | exact superpose eq85999 eq18
    | (have j1 := eq85999 X0 y
       grind)
    | exact resolve eq18 eq85999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85999
  have eq88276 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq85992 x
       have i₂ := eq87869 x
       grind)
    | (have i₁ := eq85992 y
       have i₂ := eq87869 x
       grind)
    | exact superpose eq87869 eq85992
    | (have j0 := eq85992 y
       grind)
    | exact resolve eq85992 eq87869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85992
  have eq88470 : x ≠ (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq87869
  have eq88479 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq88276
  have eq96730 : x = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq85959
       have i₂ := eq86053 y
       grind)
    | exact superpose eq86053 eq85959
    | exact resolve eq85959 eq86053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85959 eq86053
  have eq96864 : x = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq96730
  have eq96880 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq88479 eq96864
    | exact resolve eq96864 eq88479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88479 eq96864
  have eq96900 : x = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq96880
       have r₂ := eq88470
       grind)
    | exact resolve eq96880 eq88470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88470 eq96880
  have eq96915 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq928 X0 x
       have i₂ := eq96900
       grind)
    | exact superpose eq96900 eq928
    | exact resolve eq928 eq96900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97445 : x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq96900
       have i₂ := eq96915 x
       grind)
    | exact superpose eq96915 eq96900
    | exact resolve eq96900 eq96915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96900 eq96915
  have eq97600 : x = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq97445
  have eq97653 : ∀ X0 : G, x = (M.op x X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq97600 eq1207
    | exact resolve eq1207 eq97600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq97661 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq97600 eq65205
    | exact resolve eq65205 eq97600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97600
  have eq97731 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq97661 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq97661
    | (have j0 := eq97661 X0
       grind)
    | exact resolve eq97661 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97661
  have eq97843 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq97653 y
       grind)
    | exact superpose eq97653 eq18
    | (have j1 := eq97653 y
       grind)
    | exact resolve eq18 eq97653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97653
  have eq98192 : (M.op x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq97843 eq28
    | exact resolve eq28 eq97843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq98292 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq98192
    | exact resolve eq98192 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq98192
  have eq98304 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq98292
       grind)
    | exact superpose eq98292 eq18
    | exact resolve eq18 eq98292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98344 : ∀ X0 X1 X2 : G, (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x (M.op (M.op (M.op (M.op x y) X0) X1) X2)))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5264 X0 X1 X2
       have i₂ := eq98292
       grind)
    | exact superpose eq98292 eq5264
    | exact resolve eq5264 eq98292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5264 eq98292
  have eq98357 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2886 eq98344
    | exact resolve eq98344 eq2886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2886 eq98344
  have eq98397 : (σ y) = (k (σ y) (σ (M.op x (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq97843 eq98357
    | exact resolve eq98357 eq97843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98357
  have eq98412 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq98304 eq98397
    | exact resolve eq98397 eq98304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98397
  have eq98421 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq98412
    | exact resolve eq98412 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98412
  have eq98425 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq97843 eq98421
    | exact resolve eq98421 eq97843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98421
  have eq98519 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq97731 eq26
    | (have j1 := eq97731 (σ y)
       grind)
    | exact resolve eq26 eq97731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97731
  have eq99847 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq98304 eq52499
    | exact resolve eq52499 eq98304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52499
  have eq99870 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq98304 eq65205
    | exact resolve eq65205 eq98304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65205
  have eq99954 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq99870
    | (have j0 := eq99870 X0
       grind)
    | exact resolve eq99870 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99870
  have eq99960 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq99847
    | exact resolve eq99847 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99847
  have eq99976 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq97843 eq99954
    | exact resolve eq99954 eq97843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99954
  have eq99981 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq97843 eq99960
    | exact resolve eq99960 eq97843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97843 eq99960
  have eq100458 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq98425 eq788
    | (have j0 := eq788 (σ y) X0
       grind)
    | (have r₁ := eq788 (σ y) x
       have r₂ := eq98425
       grind)
    | exact resolve eq788 eq98425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788 eq98425
  have eq100463 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq100458 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100458
  have eq106444 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X1) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq99976 eq183
    | exact resolve eq183 eq99976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq99976
  have eq106734 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X1) ∨ x = (M.op x y) := by
    intro X1
    first
    | exact superpose eq26 eq106444
    | (have j0 := eq106444 X1
       grind)
    | exact resolve eq106444 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106444
  have eq204872 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (k (σ x) (σ y)) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1136 sF2 x
       have i₂ := eq100463 sF2
       grind)
    | exact superpose eq100463 eq1136
    | (have j1 := eq100463 (σ x)
       grind)
    | exact resolve eq1136 eq100463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq205313 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (k (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq934 X0 sF2
       have i₂ := eq100463 sF2
       grind)
    | (have i₁ := eq934 X0 (σ y)
       have i₂ := eq100463 sF2
       grind)
    | exact superpose eq100463 eq934
    | (have j1 := eq100463 (σ x)
       grind)
    | exact resolve eq934 eq100463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq205522 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (k (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq205313
    | (have j0 := eq205313 X0
       grind)
    | exact resolve eq205313 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205313
  have eq205790 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (k (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq204872
    | (have j0 := eq204872 X0
       grind)
    | exact resolve eq204872 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204872
  have eq205998 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq99981 eq205522
    | exact resolve eq205522 eq99981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205522
  have eq206204 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq99981 eq205790
    | exact resolve eq205790 eq99981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205790
  have eq208594 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq206204 eq1973
    | exact resolve eq1973 eq206204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1973 eq206204
  have eq208982 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106734 eq208594
    | exact resolve eq208594 eq106734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208594
  have eq209195 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq208982 eq205998
    | exact resolve eq205998 eq208982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205998 eq208982
  have eq209266 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq209195
  have eq209422 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq209266 eq100463
    | (have j0 := eq100463 (σ x)
       grind)
    | exact resolve eq100463 eq209266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100463 eq209266
  have eq209493 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq209422
  have eq209542 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq209493
    | exact resolve eq209493 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209493
  have eq209543 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq209542
  have eq209570 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq99981 eq209543
    | exact resolve eq209543 eq99981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99981 eq209543
  have eq209583 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq209570 eq27
    | exact resolve eq27 eq209570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209570
  have eq209773 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq209583
       have r₂ := eq98519
       grind)
    | exact resolve eq209583 eq98519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98519 eq209583
  have eq209873 : x = (k x (τ (M.op (σ x) (σ x)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq209773 eq52649
    | exact resolve eq52649 eq209773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52649
  have eq209888 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq209773 eq106734
    | exact resolve eq106734 eq209773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106734 eq209773
  have eq209949 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq209888 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209888
  have eq209966 : x = (k x (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq209949 eq209873
    | exact resolve eq209873 eq209949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209873 eq209949
  have eq210007 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq209966
    | exact resolve eq209966 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq209966
  have eq210890 : x ≠ x ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq773 x
       have i₂ := eq210007
       grind)
    | exact superpose eq210007 eq773
    | (have j0 := eq773 x
       grind)
    | (have r₁ := eq773 x
       have r₂ := eq210007
       grind)
    | exact resolve eq773 eq210007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773 eq210007
  have eq210905 : x = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq210890
  have eq214604 : ∀ X0 : G, (M.op X0 x) = (M.op X0 (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq928 X0 x
       have i₂ := eq210905
       grind)
    | exact superpose eq210905 eq928
    | exact resolve eq928 eq210905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq216100 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq210905
       have i₂ := eq214604 x
       grind)
    | exact superpose eq214604 eq210905
    | exact resolve eq210905 eq214604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210905 eq214604
  have eq216316 : x = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq216100
  have eq216360 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq98304 eq216316
    | exact resolve eq216316 eq98304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98304 eq216316
  have eq216361 : x = (M.op x y) := by grind
  clear eq216360
  have eq216388 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq216361
       grind)
    | exact superpose eq216361 eq18
    | exact resolve eq18 eq216361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq216389 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq216361
       grind)
    | exact superpose eq216361 eq22
    | exact resolve eq22 eq216361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq216361
  have eq216500 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq216389 eq20
    | exact resolve eq20 eq216389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216389
  have eq217475 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq216388 eq64110
    | exact resolve eq64110 eq216388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64110 eq216388
  have eq217565 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq20 eq217475
    | (have j0 := eq217475 X0
       grind)
    | exact resolve eq217475 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq217475
  have eq217571 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq216500 eq217565
    | exact resolve eq217565 eq216500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217565
  have eq218393 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq217571 eq26
    | (have j1 := eq217571 (σ y)
       grind)
    | exact resolve eq26 eq217571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq217571
  have eq219001 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq218393 eq27
    | exact resolve eq27 eq218393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq218393
  have eq219149 : False := by grind
  exact eq219149

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pxy_pyx_pxy_Equation452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq88 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq199 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq88 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq88 X0 X1
       grind)
    | exact superpose eq88 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq88 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq88 X0 X1
       grind)
    | exact resolve eq13 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq204 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq199 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq205 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq204 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq210 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq205 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq205
    | (have j0 := eq205 X0 X1
       grind)
    | exact resolve eq205 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq211 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq210 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq605 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq211 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq211
    | exact resolve eq211 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq211 x y
       grind)
    | exact superpose eq211 eq16
    | (have j1 := eq211 x y
       grind)
    | exact resolve eq16 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq629 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq605 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq605
    | (have j0 := eq605 X0 X1
       grind)
    | exact resolve eq605 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq605
  have eq631 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq629 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq629
    | exact resolve eq629 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq694 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq631 (τ X0) X1
       grind)
    | exact superpose eq631 eq18
    | (have j1 := eq631 (τ X0) X1
       grind)
    | exact resolve eq18 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq631
  have eq965 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq694 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq694
    | exact resolve eq694 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq1018 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq965 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq965
    | (have j0 := eq965 X0 X1
       grind)
    | exact resolve eq965 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq965
  have eq1134 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq613
       have i₂ := eq1018 x y
       grind)
    | exact superpose eq1018 eq613
    | (have j1 := eq1018 (σ x) (σ y)
       grind)
    | (have r₁ := eq613
       have r₂ := eq1018 x y
       grind)
    | exact resolve eq613 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1135 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1134
  have eq1192 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1135
  have eq1204 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq613
       have i₂ := eq1192
       grind)
    | exact superpose eq1192 eq613
    | exact resolve eq613 eq1192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613 eq1192
  have eq1205 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1204
  have eq1206 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1205
  have eq1241 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1206
  have eq1255 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1241
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1241
    | exact resolve eq1241 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1241
  have eq1260 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1255
       grind)
    | exact superpose eq1255 eq16
    | exact resolve eq16 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255
  have eq1320 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1260
       have i₂ := eq1018 x y
       grind)
    | exact superpose eq1018 eq1260
    | (have j1 := eq1018 x y
       grind)
    | (have r₁ := eq1260
       have r₂ := eq1018 x y
       grind)
    | exact resolve eq1260 eq1018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018
  have eq1321 : x = (M.op y y) := by grind
  clear eq1320
  have eq1325 : (M.op x y) = (k x y) := by grind
  clear eq1321
  have eq1384 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1260
       have i₂ := eq1325
       grind)
    | exact superpose eq1325 eq1260
    | exact resolve eq1260 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1260 eq1325
  have eq1387 : False := by grind
  exact eq1387
