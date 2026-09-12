import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,X) else if m(X,X) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxx_y_pxx_y_pxy_Equation4430 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
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
  clear eq35
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
  have eq178 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq16 X2 X3 (M.op x X5) X5
       have i₂ := eq16 X0 X1 x X5
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
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
  have eq180 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
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
    | (have i₁ := eq182 x x X5
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq182
    | exact resolve eq182 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq191 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq179 X0 (M.op X0 x)
       have i₂ := eq179 X0 x
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq179 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq179
    | (have j0 := eq179 x y
       grind)
    | exact resolve eq179 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : (M.op (M.op x y) y) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq179
    | (have j0 := eq179 (σ x) (σ y)
       grind)
    | exact resolve eq179 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op x y) y) := by
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
  have eq200 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X0 x) X2 X3
       have i₂ := eq179 X0 x
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq179 x x
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq179
    | exact resolve eq179 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq248 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq222 eq185
    | exact resolve eq185 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) ≠ X0 ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq185 eq13
    | (have j0 := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq185 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact resolve eq13 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq262 : ∀ X0 : G, (M.op (M.op x y) y) ≠ X0 ∨ (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) = (k (M.op (M.op (σ x) (σ y)) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq222 eq255
    | (have j0 := eq255 X0
       grind)
    | (have r₁ := eq255 (M.op (M.op x y) y)
       have r₂ := eq222
       grind)
    | exact resolve eq255 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq264 : ∀ X0 : G, (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = (k (M.op (M.op x y) y) X0) ∨ (M.op (M.op x y) y) ≠ X0 := by
    intro X0
    first
    | exact superpose eq222 eq262
    | (have j0 := eq262 X0
       grind)
    | (have r₁ := eq262 (M.op (M.op (σ x) (σ y)) (σ y))
       have r₂ := eq222
       grind)
    | exact resolve eq262 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq265 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) ∨ (M.op (M.op x y) y) ≠ X0 := by
    intro X0
    first
    | exact superpose eq191 eq264
    | (have j0 := eq264 X0
       grind)
    | (have r₁ := eq264 (M.op X0 (M.op (M.op x y) y))
       have r₂ := eq191 X0
       grind)
    | exact resolve eq264 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq272 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (M.op X0 X0) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq191 eq13
    | (have j0 := eq13 X0 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op x y) y)
       have r₂ := eq191 X0
       grind)
    | exact resolve eq13 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have j0 := eq272 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq465 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (k X0 (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | (have i₁ := eq197 X0 X0
       have i₂ := eq277 X0
       grind)
    | exact superpose eq277 eq197
    | exact resolve eq197 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq468 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) ≠ X0 ∨ (k X0 (M.op (M.op x y) y)) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq277 X0
       grind)
    | exact superpose eq277 eq13
    | exact resolve eq13 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq523 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq928 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) ∨ (k X0 (M.op (M.op x y) y)) = X0 ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq277 X0
       grind)
    | exact superpose eq277 eq11
    | exact resolve eq11 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq930 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) ∨ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = X0 ∨ (M.op (M.op x y) y) = X0 := by
    intro X0
    first
    | exact superpose eq248 eq11
    | (have j0 := eq11 (M.op (M.op x y) y) X0
       grind)
    | exact resolve eq11 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq938 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
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
  have eq940 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq985 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) ∨ (k X0 (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq928 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq1022 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) ∨ (M.op (M.op (M.op x y) y) (M.op (M.op x y) y)) = X0 := by
    intro X0
    first
    | (have j0 := eq930 X0
       have j1 := eq265 X0
       grind)
    | (have r₁ := eq930 X0
       have r₂ := eq265 (k (M.op (M.op x y) y) X0)
       grind)
    | (have r₁ := eq930 (M.op (M.op x y) y)
       have r₂ := eq265 (M.op (M.op (M.op x y) y) (M.op (M.op x y) y))
       grind)
    | (have r₁ := eq930 X0
       have r₂ := eq265 X0
       grind)
    | exact resolve eq930 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq930
  have eq1024 : ∀ X0 : G, (k X0 (M.op (M.op x y) y)) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq985 X0
       have j1 := eq468 X0
       grind)
    | (have r₁ := eq985 X0
       have r₂ := eq468 X0
       grind)
    | exact resolve eq985 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468 eq985
  have eq1050 : ∀ X0 : G, (M.op (M.op x y) y) = X0 ∨ (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq191 eq1022
    | (have j0 := eq1022 X0
       grind)
    | exact resolve eq1022 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1022
  have eq1071 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | (have j0 := eq1050 (k (M.op (M.op x y) y) X0)
       have j1 := eq265 X0
       grind)
    | (have r₁ := eq1050 X0
       have r₂ := eq265 X0
       grind)
    | (have r₁ := eq1050 (M.op (M.op x y) y)
       have r₂ := eq265 (M.op (M.op x y) y)
       grind)
    | (have r₁ := eq1050 X0
       have r₂ := eq265 (k (M.op (M.op x y) y) X0)
       grind)
    | exact resolve eq1050 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq1050
  have eq1105 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq277 (M.op sF0 y)
       have i₂ := eq1024 (M.op sF0 y)
       grind)
    | exact superpose eq1024 eq277
    | exact resolve eq277 eq1024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq1169 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq179 X0 X0
       have i₂ := eq1105 X0
       grind)
    | exact superpose eq1105 eq179
    | exact resolve eq179 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq1171 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq197 X0 X0
       have i₂ := eq1105 X0
       grind)
    | exact superpose eq1105 eq197
    | exact resolve eq197 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq1198 : ∀ X0 : G, (τ (M.op (M.op x y) y)) = (k (τ (M.op (M.op x y) y)) X0) := by
    intro X0
    first
    | exact superpose eq1071 eq523
    | exact resolve eq523 eq1071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523 eq1071
  have eq1209 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1169 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1169
    | exact resolve eq1169 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1230 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1171 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1171
    | exact resolve eq1171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171
  have eq3112 : (M.op (M.op x y) y) = (M.op (τ (M.op (M.op x y) y)) (τ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq1198 eq465
    | exact resolve eq465 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq3130 : (M.op (M.op x y) y) = (k (τ (M.op (M.op x y) y)) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq3112
       have i₂ := eq277 (τ (M.op sF0 y))
       grind)
    | exact superpose eq277 eq3112
    | exact resolve eq3112 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277 eq3112
  have eq3139 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq1198 eq3130
    | exact resolve eq3130 eq1198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198 eq3130
  have eq3154 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq3139 eq14
    | exact resolve eq14 eq3139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4889 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq938
       grind)
    | exact superpose eq938 eq40
    | exact resolve eq40 eq938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq938
  have eq4890 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4889
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4889
    | exact resolve eq4889 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4889
  have eq4892 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq4890
    | exact resolve eq4890 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4890
  have eq4894 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4892
       have i₂ := eq1105 x
       grind)
    | exact superpose eq1105 eq4892
    | exact resolve eq4892 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4892
  have eq5580 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4894 eq940
    | exact resolve eq940 eq4894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940 eq4894
  have eq5587 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq5580
       have r₂ := eq27
       grind)
    | exact resolve eq5580 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5580
  have eq5591 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5587
       have i₂ := eq1105 sF2
       grind)
    | exact superpose eq1105 eq5587
    | exact resolve eq5587 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5587
  have eq5593 : (τ (σ y)) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5591 eq97
    | exact resolve eq97 eq5591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq5591
  have eq5610 : y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq5593
    | exact resolve eq5593 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5593
  have eq5611 : y = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq5610
  have eq5621 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1169 x
       have i₂ := eq5611
       grind)
    | exact superpose eq5611 eq1169
    | exact resolve eq1169 eq5611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1169
  have eq5624 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1209 x
       have i₂ := eq5611
       grind)
    | exact superpose eq5611 eq1209
    | exact resolve eq1209 eq5611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209 eq5611
  have eq5629 : (M.op (M.op x y) y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5624
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5624
    | exact resolve eq5624 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5624
  have eq5630 : (M.op x y) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5621
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5621
    | exact resolve eq5621 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5621
  have eq5635 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5629
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5629
    | exact resolve eq5629 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5629
  have eq5639 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq5635
    | exact resolve eq5635 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5635
  have eq5640 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5630 eq5639
    | exact resolve eq5639 eq5630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5639
  have eq5645 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5640 eq195
    | exact resolve eq195 eq5640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5650 : (M.op x y) ≠ (σ y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  have eq5656 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq5645
    | exact resolve eq5645 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5645
  have eq5661 : (σ y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5640 eq5656
    | exact resolve eq5656 eq5640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5640 eq5656
  have eq5755 : (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5630 eq3154
    | exact resolve eq3154 eq5630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3154 eq5630
  have eq5785 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq5755
    | exact resolve eq5755 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5755
  have eq5890 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5785 eq195
    | exact resolve eq195 eq5785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq5900 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq5890
    | exact resolve eq5890 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5890
  have eq5905 : (σ y) = (M.op (M.op x y) y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5785 eq5900
    | exact resolve eq5900 eq5785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5900
  have eq6935 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5661 eq191
    | exact resolve eq191 eq5661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq6987 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5661 eq3139
    | exact resolve eq3139 eq5661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5661
  have eq7027 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq6987
    | exact resolve eq6987 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6987
  have eq7142 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7027 eq27
    | exact resolve eq27 eq7027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7027
  have eq7376 : (σ y) = (τ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5905 eq3139
    | exact resolve eq3139 eq5905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3139 eq5905
  have eq7416 : y = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq7376
    | exact resolve eq7376 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq7376
  have eq7466 : y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq7416
       have r₂ := eq7142
       grind)
    | exact resolve eq7416 eq7142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7142 eq7416
  have eq7509 : (M.op x y) = (M.op x (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq7466
       grind)
    | exact superpose eq7466 eq18
    | exact resolve eq18 eq7466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7575 : (M.op x y) ≠ (σ y) ∨ y = (M.op x y) := by grind
  clear eq7466
  have eq7830 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6935 eq7509
    | exact resolve eq7509 eq6935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6935 eq7509
  have eq7840 : (M.op x y) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) := by grind
  clear eq7830
  have eq7849 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq7840
       have r₂ := eq5650
       grind)
    | exact resolve eq7840 eq5650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5650 eq7840
  have eq7891 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7849 eq27
    | exact resolve eq27 eq7849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7900 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7849 eq5785
    | exact resolve eq5785 eq7849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5785 eq7849
  have eq7901 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq7900
  have eq7904 : (M.op x y) = (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq7901
       have r₂ := eq7575
       grind)
    | exact resolve eq7901 eq7575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7575 eq7901
  have eq7911 : y = (M.op x y) := by
    first
    | (have r₁ := eq7904
       have r₂ := eq7891
       grind)
    | exact resolve eq7904 eq7891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7891 eq7904
  have eq7916 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq7911
       grind)
    | exact superpose eq7911 eq18
    | exact resolve eq18 eq7911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq7917 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq7911
       grind)
    | exact superpose eq7911 eq24
    | exact resolve eq24 eq7911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq8132 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq7917 eq20
    | exact resolve eq20 eq7917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7917
  have eq8270 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq7916 eq194
    | exact resolve eq194 eq7916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq7916
  have eq8301 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq8270
       have i₂ := eq7911
       grind)
    | exact superpose eq7911 eq8270
    | exact resolve eq8270 eq7911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8270
  have eq8308 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq8301
       have i₂ := eq1105 sF0
       grind)
    | exact superpose eq1105 eq8301
    | exact resolve eq8301 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8301
  have eq8311 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq8308 eq37
    | exact resolve eq37 eq8308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq8319 : (M.op (M.op x y) y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq8308 eq1230
    | exact resolve eq1230 eq8308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230
  have eq8331 : (M.op (M.op x y) y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq8319
       have i₂ := eq1105 (σ sF0)
       grind)
    | exact superpose eq1105 eq8319
    | exact resolve eq8319 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8319
  have eq8338 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq8311
    | exact resolve eq8311 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8311
  have eq8340 : (σ (k (M.op x y) (M.op x y))) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq8331
       have i₂ := eq10 sF0 sF0
       grind)
    | exact superpose eq10 eq8331
    | exact resolve eq8331 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8331
  have eq8346 : (σ y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq8132 eq8338
    | exact resolve eq8338 eq8132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8338
  have eq8348 : (σ (k (M.op x y) (M.op x y))) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq8340
       have i₂ := eq7911
       grind)
    | exact superpose eq7911 eq8340
    | exact resolve eq8340 eq7911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8340
  have eq8353 : (k (M.op x y) (M.op x y)) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq8348
       have i₂ := eq1105 sF0
       grind)
    | exact superpose eq1105 eq8348
    | exact resolve eq8348 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8348
  have eq8356 : (k (M.op x y) (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq41 eq8353
    | exact resolve eq8353 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq8353
  have eq8358 : (k (σ (M.op x y)) (σ y)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq8132 eq8356
    | exact resolve eq8356 eq8132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8356
  have eq8360 : (M.op x y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq8308 eq8358
    | exact resolve eq8358 eq8308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8358
  have eq8362 : (M.op x y) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq8360
    | exact resolve eq8360 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8360
  have eq8364 : (M.op x y) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq8132 eq8362
    | exact resolve eq8362 eq8132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8132 eq8362
  have eq8439 : (M.op x y) = (σ y) := by
    first
    | exact superpose eq8364 eq8346
    | exact resolve eq8346 eq8364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8346
  have eq8440 : (k y y) = (τ (M.op x y)) := by
    first
    | exact superpose eq8364 eq115
    | exact resolve eq115 eq8364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq8364
  have eq8465 : (k (M.op x y) (M.op x y)) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq8440
       have i₂ := eq7911
       grind)
    | exact superpose eq7911 eq8440
    | exact resolve eq8440 eq7911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8440
  have eq8472 : (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq8308 eq8465
    | exact resolve eq8465 eq8308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8465
  have eq8490 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq8439 eq26
    | exact resolve eq26 eq8439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq8504 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq8439 eq222
    | exact resolve eq222 eq8439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq8439
  have eq8534 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | (have i₁ := eq8504
       have i₂ := eq7911
       grind)
    | exact superpose eq7911 eq8504
    | exact resolve eq8504 eq7911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8504
  have eq8551 : (k (M.op x y) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | (have i₁ := eq8534
       have i₂ := eq1105 sF0
       grind)
    | exact superpose eq1105 eq8534
    | exact resolve eq8534 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8534
  have eq8565 : (M.op x y) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq8308 eq8551
    | exact resolve eq8551 eq8308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8551
  have eq8586 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq8472 eq14
    | exact resolve eq14 eq8472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8472
  have eq8608 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq8586 eq20
    | exact resolve eq20 eq8586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq8586
  have eq8747 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq8490 eq200
    | exact resolve eq200 eq8490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq8750 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq8565 eq8747
    | exact resolve eq8747 eq8565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8565 eq8747
  have eq8764 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq8750 X0
       have i₂ := eq7911
       grind)
    | exact superpose eq7911 eq8750
    | exact resolve eq8750 eq7911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7911 eq8750
  have eq8768 : ∀ X0 : G, (M.op x y) = (M.op X0 (k (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq8764 X0
       have i₂ := eq1105 sF0
       grind)
    | exact superpose eq1105 eq8764
    | exact resolve eq8764 eq1105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1105 eq8764
  have eq8771 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq8308 eq8768
    | exact resolve eq8768 eq8308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8308 eq8768
  have eq9153 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8771 eq8490
    | exact resolve eq8490 eq8771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8490 eq8771
  have eq9231 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq9153 eq27
    | exact resolve eq27 eq9153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq9153
  have eq9252 : False := by grind
  exact eq9252

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_pyy_pxx_pyy_pyx_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
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
  have eq54 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X2 X3 (M.op x X5) X5
       have i₂ := eq14 X0 X1 x X5
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq77
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq77 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90
    | exact resolve eq90 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq96
    | exact resolve eq96 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq98
    | exact resolve eq98 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq112 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x y) ∨ (k y x) = (M.op x x) := by
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
  have eq113 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq114 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq114 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq114 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq115 (σ X0)
       grind)
    | exact superpose eq115 eq10
    | exact resolve eq10 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq115 x
       grind)
    | exact superpose eq115 eq43
    | exact resolve eq43 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq123 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq118
       have i₂ := eq115 sF2
       grind)
    | exact superpose eq115 eq118
    | exact resolve eq118 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq124 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq117 X0
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq117
    | exact resolve eq117 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq260 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq55 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55
    | (have j0 := eq55 x y
       grind)
    | exact resolve eq55 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x x
       have i₂ := eq14 x x X0 X1
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x (M.op x y)) y) := by
    intro X0 X1
    first
    | exact superpose eq260 eq14
    | exact resolve eq14 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq273 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) y) := by
    first
    | (have i₁ := eq272 x x
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq272
    | exact resolve eq272 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq274 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq260 eq273
    | exact resolve eq273 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq283 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq56 x x
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq284 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq260 eq283
    | exact resolve eq283 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq287 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq284 eq14
    | exact resolve eq14 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq287 x x
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq287
    | exact resolve eq287 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq290 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | exact superpose eq260 eq288
    | exact resolve eq288 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq331 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq115 (τ X0)
       grind)
    | exact superpose eq115 eq34
    | exact resolve eq34 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq342 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq331 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq331
    | exact resolve eq331 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq344 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq342 X0
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq342
    | exact resolve eq342 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq342
  have eq443 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op x (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq260 eq262
    | exact resolve eq262 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq601 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op x y) y) X5) := by
    intro X2 X3 X5
    first
    | (have i₁ := eq54 x x X2 X3 X5
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq54
    | exact resolve eq54 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq602 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X2 X3 X5
    first
    | exact superpose eq260 eq601
    | exact resolve eq601 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq603 : ∀ X5 : G, (M.op (M.op x y) y) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | (have i₁ := eq602 x x X5
       have i₂ := eq55 x x
       grind)
    | exact superpose eq55 eq602
    | exact resolve eq602 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq604 : ∀ X5 : G, (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) X5) := by
    intro X5
    first
    | exact superpose eq260 eq603
    | exact resolve eq603 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq668 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq443 (σ X0) (σ X0)
       have i₂ := eq124 X0
       grind)
    | exact superpose eq124 eq443
    | exact resolve eq443 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq840 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq344 X0
       grind)
    | exact superpose eq344 eq16
    | exact resolve eq16 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq1023 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq55 (τ X0) (τ X0)
       have i₂ := eq840 X0
       grind)
    | exact superpose eq840 eq55
    | exact resolve eq55 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1030 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq260 eq1023
    | exact resolve eq1023 eq260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq1413 : (M.op x (M.op x y)) = (M.op (σ (M.op x (M.op x y))) (σ (M.op x (M.op x y)))) := by
    first
    | exact superpose eq604 eq668
    | exact resolve eq668 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq1475 : (M.op x (M.op x y)) = (σ (M.op (M.op x (M.op x y)) (M.op x (M.op x y)))) := by
    first
    | (have i₁ := eq1413
       have i₂ := eq124 (M.op x sF0)
       grind)
    | exact superpose eq124 eq1413
    | exact resolve eq1413 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq1413
  have eq1490 : (M.op x (M.op x y)) = (σ (M.op x (M.op x y))) := by
    first
    | exact superpose eq604 eq1475
    | exact resolve eq1475 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604 eq1475
  have eq1495 : (M.op x (M.op x y)) = (τ (M.op x (M.op x y))) := by
    first
    | exact superpose eq1490 eq16
    | exact resolve eq16 eq1490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1490
  have eq16516 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16523 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq16516
    | exact resolve eq16516 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16516
  have eq16534 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16523
       have r₂ := eq27
       grind)
    | exact resolve eq16523 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16523
  have eq16538 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq16534
    | exact resolve eq16534 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16534
  have eq16540 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq16538
    | exact resolve eq16538 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16538
  have eq16542 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16540 eq113
    | (have r₁ := eq113
       have r₂ := eq16540
       grind)
    | exact resolve eq113 eq16540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113 eq16540
  have eq16564 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq16542
  have eq16565 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq16564
  have eq16577 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16565 eq99
    | exact resolve eq99 eq16565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq16565
  have eq16591 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16577
  have eq16593 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16591
       have r₂ := eq27
       grind)
    | exact resolve eq16591 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16591
  have eq16597 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq112
       have i₂ := eq16593
       grind)
    | exact superpose eq16593 eq112
    | (have r₁ := eq112
       have r₂ := eq16593
       grind)
    | exact resolve eq112 eq16593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq16598 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq123
       have i₂ := eq16593
       grind)
    | exact superpose eq16593 eq123
    | exact resolve eq123 eq16593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123 eq16593
  have eq16617 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16597
  have eq16618 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16617
  have eq16629 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq16598
    | exact resolve eq16598 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16598
  have eq16636 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq16618
       grind)
    | exact superpose eq16618 eq77
    | exact resolve eq77 eq16618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq16618
  have eq16662 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq16636
    | exact resolve eq16636 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16636
  have eq16775 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16662 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq16662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16662
  have eq16784 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16775
    | exact resolve eq16775 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16775
  have eq16795 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16784
       have r₂ := eq27
       grind)
    | exact resolve eq16784 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16784
  have eq16799 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16795
    | exact resolve eq16795 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16795
  have eq16801 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16799
    | exact resolve eq16799 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16799
  have eq16802 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16801
  have eq16814 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16802 eq16629
    | exact resolve eq16629 eq16802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16629 eq16802
  have eq16829 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16814
  have eq16838 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16829
       have r₂ := eq27
       grind)
    | exact resolve eq16829 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16829
  have eq16980 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16838 eq284
    | exact resolve eq284 eq16838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq16983 : (M.op (σ x) (σ y)) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq16980
    | exact resolve eq16980 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16980
  have eq17135 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16983 eq274
    | exact resolve eq274 eq16983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq17158 : (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16983 eq1495
    | exact resolve eq1495 eq16983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495 eq16983
  have eq17229 : (σ x) = (τ (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16838 eq17158
    | exact resolve eq17158 eq16838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17158
  have eq17265 : (σ x) = (τ (σ x)) ∨ x = (M.op x y) := by grind
  clear eq17229
  have eq17267 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq17265
    | exact resolve eq17265 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq17265
  have eq17737 : (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16838 eq17135
    | exact resolve eq17135 eq16838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16838 eq17135
  have eq17744 : (σ x) = (M.op (σ x) y) ∨ x = (M.op x y) := by grind
  clear eq17737
  have eq18142 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17267 eq17744
    | exact resolve eq17744 eq17267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17267 eq17744
  have eq18149 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq18142
  have eq18152 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18149
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18149
    | exact resolve eq18149 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18149
  have eq18153 : x = (M.op x y) := by grind
  clear eq18152
  have eq18291 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq18153 eq20
    | exact resolve eq20 eq18153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq18337 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq18153 eq260
    | exact resolve eq260 eq18153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq18344 : (M.op x x) = (M.op (M.op x x) (σ y)) := by
    first
    | exact superpose eq18153 eq290
    | exact resolve eq290 eq18153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290
  have eq18378 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18337
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq18337
    | exact resolve eq18337 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq18337
  have eq18423 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18291
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18291
    | exact resolve eq18291 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18291
  have eq18424 : x = (M.op x x) := by
    first
    | exact superpose eq18153 eq18378
    | exact resolve eq18378 eq18153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18378
  have eq18440 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq18423 eq26
    | exact resolve eq26 eq18423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq18620 : (M.op x (M.op x y)) = (M.op (τ x) (τ x)) := by
    first
    | (have i₁ := eq1030 x
       have i₂ := eq18424
       grind)
    | exact superpose eq18424 eq1030
    | exact resolve eq1030 eq18424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq18631 : (M.op x (M.op x y)) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq18620
       have i₂ := eq840 x
       grind)
    | exact superpose eq840 eq18620
    | exact resolve eq18620 eq840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840 eq18620
  have eq18644 : (M.op x (M.op x y)) = (τ x) := by
    first
    | (have i₁ := eq18631
       have i₂ := eq18424
       grind)
    | exact superpose eq18424 eq18631
    | exact resolve eq18631 eq18424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18631
  have eq18657 : (M.op x x) = (τ x) := by
    first
    | exact superpose eq18153 eq18644
    | exact resolve eq18644 eq18153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18153 eq18644
  have eq18669 : x = (τ x) := by
    first
    | (have i₁ := eq18657
       have i₂ := eq18424
       grind)
    | exact superpose eq18424 eq18657
    | exact resolve eq18657 eq18424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18657
  have eq18681 : x = (σ x) := by
    first
    | (have i₁ := eq15 x
       have i₂ := eq18669
       grind)
    | exact superpose eq18669 eq15
    | exact resolve eq15 eq18669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18669
  have eq18741 : x = (σ x) := by
    first
    | (have i₁ := eq18681
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18681
    | exact resolve eq18681 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq18681
  have eq18759 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq18423 eq18741
    | exact resolve eq18741 eq18423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18423 eq18741
  have eq19095 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq18759 eq18440
    | exact resolve eq18440 eq18759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18440
  have eq20308 : x = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18344
       have i₂ := eq18424
       grind)
    | exact superpose eq18424 eq18344
    | exact resolve eq18344 eq18424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18344 eq18424
  have eq20309 : x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19095 eq20308
    | exact resolve eq20308 eq19095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19095 eq20308
  have eq20311 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq20309 eq27
    | exact resolve eq27 eq20309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20309
  have eq20333 : False := by grind
  exact eq20333

/-- `Equation4430`: `x ◇ (x ◇ y) = (z ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyy_y_pyx_pxx_pxy_Equation4430 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4430 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4430.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X2 X3) X3) := by
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
  have eq174 : ∀ X0 X1 X2 X4 X5 : G, (M.op (M.op X4 X5) X5) = (M.op X2 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1 X2 X4 X5
    first
    | (have i₁ := eq16 X2 (M.op X2 x) X4 X5
       have i₂ := eq16 X2 x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X4 X5 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X4 X5) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq16 x x X4 X5
       have i₂ := eq16 x x X0 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op X0 (M.op X0 X1)) X5) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq16 X2 X3 (M.op x X5) X5
       have i₂ := eq16 X0 X1 x X5
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) y) := by
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
  have eq180 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 X1 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X2 X3 X5 : G, (M.op X2 (M.op X2 X3)) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X5) := by
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
    | (have i₁ := eq182 x x X5
       have i₂ := eq180 x x
       grind)
    | exact superpose eq180 eq182
    | exact resolve eq182 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq186 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq186 X0
       have i₂ := eq180 X0 X0
       grind)
    | exact superpose eq180 eq186
    | exact resolve eq186 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq188 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq179 X0 (M.op X0 x)
       have i₂ := eq179 X0 x
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq179 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq179
    | (have j0 := eq179 x y
       grind)
    | exact resolve eq179 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op (M.op x y) y) := by
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
  have eq196 : ∀ X0 X2 X3 : G, (M.op (M.op X2 X3) X3) = (M.op X0 (M.op (M.op x y) y)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq16 X0 (M.op X0 x) X2 X3
       have i₂ := eq179 X0 x
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : (M.op (M.op x y) y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
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
  have eq240 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op (M.op x y) y) X0) := by
    intro X0
    first
    | exact superpose eq216 eq185
    | exact resolve eq185 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : (M.op (M.op (σ x) (σ y)) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) := by
    first
    | exact superpose eq185 eq187
    | exact resolve eq187 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq260 : (σ (M.op (M.op (σ x) (σ y)) (σ y))) = (k (σ (M.op y y)) (σ y)) := by
    first
    | (have i₁ := eq40 (M.op y y)
       have i₂ := eq187 y
       grind)
    | exact superpose eq187 eq40
    | exact resolve eq40 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : (k (σ (M.op y y)) (σ y)) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq216 eq260
    | exact resolve eq260 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260
  have eq265 : (M.op (M.op x y) y) = (k (M.op (M.op x y) y) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq216 eq258
    | exact resolve eq258 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq496 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq543 : ∀ X0 : G, (σ (M.op (M.op (σ x) (σ y)) (σ y))) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq38 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq187 (τ X0)
       grind)
    | exact superpose eq187 eq38
    | exact resolve eq38 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq575 : ∀ X0 : G, (σ (M.op (M.op x y) y)) = (k (σ (M.op (τ X0) (τ X0))) X0) := by
    intro X0
    first
    | exact superpose eq216 eq543
    | exact resolve eq543 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq595 : ∀ X0 : G, (τ (M.op (M.op (σ x) (σ y)) (σ y))) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq496 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq187 (σ X0)
       grind)
    | exact superpose eq187 eq496
    | exact resolve eq496 eq187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq617 : ∀ X0 : G, (τ (M.op (M.op x y) y)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | exact superpose eq216 eq595
    | exact resolve eq595 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq595
  have eq1258 : (M.op x y) = (k x y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
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
  have eq1266 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq1272 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1273 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1272 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1272
  have eq1331 : ∀ X0 : G, (M.op (M.op x y) y) ≠ (M.op (M.op x y) y) ∨ (M.op (M.op x y) y) = X0 ∨ (M.op X0 X0) = (k X0 (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq240 eq12
    | (have j0 := eq12 (k X0 (M.op (M.op x y) y)) X0
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op x y) y)
       have r₂ := eq240 (M.op (M.op x y) y)
       grind)
    | exact resolve eq12 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240
  have eq1332 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) y)) ∨ (M.op (M.op x y) y) = X0 := by
    intro X0
    first
    | (have j0 := eq1331 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331
  have eq1342 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1273 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1273
    | (have j0 := eq1273 (σ X0)
       grind)
    | exact resolve eq1273 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273
  have eq2443 : ∀ X0 : G, (τ (σ (M.op (M.op x y) y))) = (k (τ (σ (M.op (τ (σ X0)) (τ (σ X0))))) X0) := by
    intro X0
    first
    | (have i₁ := eq496 (σ (M.op (τ (σ X0)) (τ (σ X0)))) X0
       have i₂ := eq575 (σ X0)
       grind)
    | exact superpose eq575 eq496
    | exact resolve eq496 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq2455 : ∀ X0 : G, (τ (σ (M.op (M.op x y) y))) = (k (M.op (τ (σ X0)) (τ (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq2443 X0
       have i₂ := eq15 (M.op (τ (σ X0)) (τ (σ X0)))
       grind)
    | exact superpose eq15 eq2443
    | exact resolve eq2443 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2443
  have eq2473 : ∀ X0 : G, (k (M.op X0 X0) X0) = (τ (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | (have i₁ := eq2455 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq2455
    | exact resolve eq2455 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2455
  have eq2491 : ∀ X0 : G, (M.op (M.op x y) y) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2473 X0
       have i₂ := eq15 (M.op sF0 y)
       grind)
    | exact superpose eq15 eq2473
    | exact resolve eq2473 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2473
  have eq3092 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1258
       grind)
    | exact superpose eq1258 eq40
    | exact resolve eq40 eq1258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3093 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3092
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3092
    | exact resolve eq3092 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3092
  have eq3095 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq3093
    | exact resolve eq3093 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3093
  have eq17239 : (σ (M.op (M.op x y) y)) ≠ (σ (M.op (M.op x y) y)) ∨ (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    first
    | exact superpose eq265 eq1342
    | (have j0 := eq1342 (M.op (M.op x y) y)
       grind)
    | exact resolve eq1342 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342
  have eq17275 : (σ (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by grind
  clear eq17239
  have eq17390 : (τ (M.op (M.op x y) y)) = (k (τ (σ (M.op (M.op x y) y))) (M.op (M.op x y) y)) := by
    first
    | exact superpose eq17275 eq617
    | exact resolve eq617 eq17275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17411 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = (M.op (σ (M.op (M.op x y) y)) (σ (M.op (M.op x y) y))) := by
    intro X0
    first
    | exact superpose eq17275 eq196
    | exact resolve eq196 eq17275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17417 : ∀ X0 : G, (M.op X0 (M.op (M.op x y) y)) = (σ (M.op (M.op x y) y)) := by
    intro X0
    first
    | exact superpose eq17275 eq17411
    | exact resolve eq17411 eq17275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17275 eq17411
  have eq17433 : (k (M.op (M.op x y) y) (M.op (M.op x y) y)) = (τ (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq17390
       have i₂ := eq15 (M.op sF0 y)
       grind)
    | exact superpose eq15 eq17390
    | exact resolve eq17390 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17390
  have eq17435 : (M.op (M.op x y) y) = (σ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq188 eq17417
    | exact resolve eq17417 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17417
  have eq17449 : (M.op (M.op x y) y) = (τ (M.op (M.op x y) y)) := by
    first
    | exact superpose eq265 eq17433
    | exact resolve eq17433 eq265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265 eq17433
  have eq18555 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3095 eq1266
    | exact resolve eq1266 eq3095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18562 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18555
       have r₂ := eq27
       grind)
    | exact resolve eq18555 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18555
  have eq18585 : (M.op (M.op x y) y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18562 eq194
    | exact resolve eq194 eq18562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18594 : (σ y) = (M.op (M.op x y) y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18562 eq18585
    | exact resolve eq18585 eq18562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18585
  have eq18640 : (σ y) = (τ (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18594 eq17449
    | exact resolve eq17449 eq18594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18678 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq18640
    | exact resolve eq18640 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq18640
  have eq18713 : (k (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18678 eq2491
    | exact resolve eq2491 eq18678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18729 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18678 eq194
    | exact resolve eq194 eq18678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18678
  have eq18738 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26 eq18729
    | exact resolve eq18729 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18729
  have eq18750 : (σ (M.op x y)) = (M.op (M.op x y) y) ∨ y = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3095 eq18713
    | exact resolve eq18713 eq3095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3095 eq18713
  have eq29510 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18750 eq18738
    | exact resolve eq18738 eq18750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18738 eq18750
  have eq29553 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (σ y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq29510
  have eq29580 : y = (M.op y y) ∨ y = (σ y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq29553
       have r₂ := eq27
       grind)
    | exact resolve eq29553 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29553
  have eq29626 : (M.op (M.op x y) y) = (M.op y y) ∨ y = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq194 y y
       have i₂ := eq29580
       grind)
    | exact superpose eq29580 eq194
    | exact resolve eq194 eq29580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29649 : y = (M.op (M.op x y) y) ∨ y = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29580 eq29626
    | exact resolve eq29626 eq29580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29580 eq29626
  have eq29705 : y = (σ y) ∨ y = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29649 eq17435
    | exact resolve eq17435 eq29649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29649
  have eq29771 : y = (σ y) ∨ y = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq29705
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq29705
    | exact resolve eq29705 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29705
  have eq29772 : x = (M.op y y) ∨ y = (σ y) := by grind
  clear eq29771
  have eq29798 : (k (σ x) (σ y)) = (σ (M.op (M.op x y) y)) ∨ y = (σ y) := by
    first
    | (have i₁ := eq263
       have i₂ := eq29772
       grind)
    | exact superpose eq29772 eq263
    | exact resolve eq263 eq29772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29804 : (k x y) = (M.op (M.op x y) y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq2491 y
       have i₂ := eq29772
       grind)
    | exact superpose eq29772 eq2491
    | exact resolve eq2491 eq29772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2491
  have eq29809 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op x y)) ∨ y = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq174 y y X2 X0 X1
       have i₂ := eq29772
       grind)
    | exact superpose eq29772 eq174
    | exact resolve eq174 eq29772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29819 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq194 y y
       have i₂ := eq29772
       grind)
    | exact superpose eq29772 eq194
    | exact resolve eq194 eq29772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29849 : (M.op x y) = (M.op (M.op x y) y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq29819
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29819
    | exact resolve eq29819 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29819
  have eq29858 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op x y)) ∨ y = (σ y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29809 X0 X1 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq29809
    | (have j0 := eq29809 X0 X1 X2
       grind)
    | exact resolve eq29809 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29809
  have eq29861 : (k (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (σ y) := by
    first
    | exact superpose eq17435 eq29798
    | exact resolve eq29798 eq17435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29798
  have eq29869 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op x y)) ∨ y = (σ y) := by
    intro X2
    first
    | (have i₁ := eq29858 x x X2
       have i₂ := eq194 x x
       grind)
    | (have i₁ := eq29858 x y X2
       have i₂ := eq194 X2 x
       grind)
    | exact superpose eq194 eq29858
    | (have j0 := eq29858 x y X2
       grind)
    | exact resolve eq29858 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29858
  have eq29871 : (k (σ x) (σ y)) = (M.op (M.op x y) y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq29861
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq29861
    | exact resolve eq29861 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29861
  have eq29873 : ∀ X2 : G, (M.op x y) = (M.op X2 (M.op x y)) ∨ y = (σ y) := by
    intro X2
    first
    | exact superpose eq29849 eq29869
    | exact resolve eq29869 eq29849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29869
  have eq29875 : (M.op x y) = (k (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq29849 eq29871
    | exact resolve eq29871 eq29849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29871
  have eq29896 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x y)) ∨ (M.op x y) = X0 ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq29849 eq1332
    | exact resolve eq1332 eq29849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29899 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq29849 eq17435
    | exact resolve eq17435 eq29849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29928 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op X0 (M.op x y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq29849 eq196
    | exact resolve eq196 eq29849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196 eq29849
  have eq29956 : ∀ X0 : G, (k x y) = (M.op X0 (M.op x y)) ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq29804 eq29928
    | exact resolve eq29928 eq29804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29928
  have eq29965 : (M.op x y) = (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq20 eq29899
    | exact resolve eq29899 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29899
  have eq29974 : (M.op x y) = (k x y) ∨ y = (σ y) := by
    first
    | exact superpose eq29873 eq29956
    | exact resolve eq29956 eq29873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29956
  have eq30367 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq29875 eq1266
    | exact resolve eq1266 eq29875
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266 eq29875
  have eq32962 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (k X0 (M.op x y)) X0) ∨ (M.op x y) = X0 ∨ y = (σ y) := by
    intro X0
    first
    | (have i₁ := eq194 X0 X0
       have i₂ := eq29896 X0
       grind)
    | exact superpose eq29896 eq194
    | (have j1 := eq29896 X0
       grind)
    | exact resolve eq194 eq29896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33003 : x = (k y (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) ∨ y = (σ y) := by
    first
    | (have i₁ := eq29772
       have i₂ := eq29896 y
       grind)
    | exact superpose eq29896 eq29772
    | (have j1 := eq29896 y
       grind)
    | exact resolve eq29772 eq29896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29772 eq29896
  have eq33028 : x = (k y (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by grind
  clear eq33003
  have eq33091 : ∀ X0 : G, (k x y) = (M.op (k X0 (M.op x y)) X0) ∨ (M.op x y) = X0 ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq29804 eq32962
    | (have j0 := eq32962 X0
       grind)
    | exact resolve eq32962 eq29804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32962
  have eq33143 : ∀ X0 : G, (M.op x y) = (M.op (k X0 (M.op x y)) X0) ∨ (M.op x y) = X0 ∨ y = (σ y) := by
    intro X0
    first
    | exact superpose eq29974 eq33091
    | (have j0 := eq33091 (M.op (k X0 (M.op x y)) X0)
       grind)
    | exact resolve eq33091 eq29974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33091
  have eq33230 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33028 eq41
    | exact resolve eq41 eq33028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq33028
  have eq33252 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33230
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33230
    | exact resolve eq33230 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33230
  have eq33256 : (σ x) = (k (σ y) (σ (M.op x y))) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq33252
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq33252
    | exact resolve eq33252 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33252
  have eq33260 : (σ x) = (k (σ y) (M.op x y)) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29965 eq33256
    | exact resolve eq33256 eq29965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33256
  have eq33311 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (σ y) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq33260 eq33143
    | (have j0 := eq33143 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq33143 eq33260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33143 eq33260
  have eq33365 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (σ y) ∨ y = (M.op x y) := by grind
  clear eq33311
  have eq33393 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq33365
    | exact resolve eq33365 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33365
  have eq37974 : (M.op (M.op x y) y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq30367 eq194
    | exact resolve eq194 eq30367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38001 : (σ y) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq30367 eq37974
    | exact resolve eq37974 eq30367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30367 eq37974
  have eq38019 : (σ y) = (k x y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq29804 eq38001
    | exact resolve eq38001 eq29804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29804 eq38001
  have eq38034 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq29974 eq38019
    | exact resolve eq38019 eq29974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29974 eq38019
  have eq38093 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq38034 eq194
    | exact resolve eq194 eq38034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38034
  have eq38118 : (M.op (σ x) (σ y)) = (M.op (M.op x y) y) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq26 eq38093
    | exact resolve eq38093 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38093
  have eq38141 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq33393 eq38118
    | exact resolve eq38118 eq33393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33393 eq38118
  have eq38156 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq29873 eq38141
    | exact resolve eq38141 eq29873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38141
  have eq38157 : (M.op x y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ y = (σ y) := by grind
  clear eq38156
  have eq38169 : (M.op x y) ≠ (σ (M.op x y)) ∨ (M.op x y) = (σ y) ∨ y = (σ y) := by
    first
    | exact superpose eq38157 eq27
    | exact resolve eq27 eq38157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38157
  have eq38224 : (M.op x y) = (σ y) ∨ y = (σ y) := by
    first
    | (have r₁ := eq38169
       have r₂ := eq29965
       grind)
    | exact resolve eq38169 eq29965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38169
  have eq38231 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq38224 eq26
    | exact resolve eq26 eq38224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38224
  have eq38405 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (σ y) := by
    first
    | exact superpose eq29873 eq38231
    | exact resolve eq38231 eq29873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29873 eq38231
  have eq38499 : (M.op x y) ≠ (σ (M.op x y)) ∨ y = (σ y) := by
    first
    | exact superpose eq38405 eq27
    | exact resolve eq27 eq38405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38405
  have eq38552 : y = (σ y) := by
    first
    | (have r₁ := eq38499
       have r₂ := eq29965
       grind)
    | exact resolve eq38499 eq29965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29965 eq38499
  have eq38559 : (M.op x y) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq38552
       grind)
    | exact superpose eq38552 eq18
    | exact resolve eq18 eq38552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq38560 : (σ y) = (σ (σ y)) := by
    first
    | (have i₁ := eq24
       have i₂ := eq38552
       grind)
    | exact superpose eq38552 eq24
    | exact resolve eq24 eq38552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq38561 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq38552
       grind)
    | exact superpose eq38552 eq36
    | exact resolve eq36 eq38552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq38562 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq38552
       grind)
    | exact superpose eq38552 eq40
    | exact resolve eq40 eq38552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq38563 : ∀ X0 : G, (M.op (M.op x y) (σ y)) = (M.op X0 (M.op (M.op x y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq188 X0
       have i₂ := eq38552
       grind)
    | exact superpose eq38552 eq188
    | exact resolve eq188 eq38552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq38571 : (k (σ (M.op (σ y) (σ y))) (σ y)) = (σ (M.op (M.op x y) (σ y))) := by
    first
    | (have i₁ := eq263
       have i₂ := eq38552
       grind)
    | exact superpose eq38552 eq263
    | exact resolve eq263 eq38552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq38589 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (k x (σ y)) ∨ x = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1258
       have i₂ := eq38552
       grind)
    | exact superpose eq38552 eq1258
    | exact resolve eq1258 eq38552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1258
  have eq38590 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) (σ y))) ∨ (M.op (M.op x y) (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1332 X0
       have i₂ := eq38552
       grind)
    | exact superpose eq38552 eq1332
    | exact resolve eq1332 eq38552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38594 : (M.op (M.op x y) (σ y)) = (σ (M.op (M.op x y) (σ y))) := by
    first
    | (have i₁ := eq17435
       have i₂ := eq38552
       grind)
    | exact superpose eq38552 eq17435
    | exact resolve eq17435 eq38552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38595 : (M.op (M.op x y) (σ y)) = (τ (M.op (M.op x y) (σ y))) := by
    first
    | (have i₁ := eq17449
       have i₂ := eq38552
       grind)
    | exact superpose eq38552 eq17449
    | exact resolve eq17449 eq38552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38600 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq18594
       have i₂ := eq38552
       grind)
    | exact superpose eq38552 eq18594
    | exact resolve eq18594 eq38552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18594
  have eq38606 : (M.op (M.op x y) (σ y)) = (k (σ (M.op (σ y) (σ y))) (σ y)) := by
    first
    | exact superpose eq38594 eq38571
    | exact resolve eq38571 eq38594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38571
  have eq38689 : ∀ X0 : G, (τ (k X0 (σ y))) = (k (τ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq38560 eq496
    | exact resolve eq496 eq38560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq39226 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op x y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq38559 eq16
    | exact resolve eq16 eq38559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39229 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op x y) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq38559 eq176
    | exact resolve eq176 eq38559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq39669 : (k (σ y) (σ (M.op (M.op x y) y))) = (σ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1332 eq38561
    | (have j1 := eq1332 (σ y)
       grind)
    | exact resolve eq38561 eq1332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1332 eq38561
  have eq39890 : (k (σ y) (M.op (M.op x y) y)) = (σ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq17435 eq39669
    | exact resolve eq39669 eq17435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17435 eq39669
  have eq39965 : (σ (M.op (σ y) (σ y))) = (k (σ y) (M.op (M.op x y) (σ y))) ∨ (σ y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq39890
       have i₂ := eq38552
       grind)
    | exact superpose eq38552 eq39890
    | exact resolve eq39890 eq38552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39890
  have eq39993 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (σ (M.op (σ y) (σ y))) = (k (σ y) (M.op (M.op x y) (σ y))) := by
    first
    | (have i₁ := eq39965
       have i₂ := eq38552
       grind)
    | exact superpose eq38552 eq39965
    | exact resolve eq39965 eq38552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39965
  have eq39994 : (M.op (σ y) (σ y)) = (σ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq38590 eq39993
    | (have j1 := eq38590 (σ y)
       grind)
    | exact resolve eq39993 eq38590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38590 eq39993
  have eq40708 : (τ (τ (M.op (M.op x y) y))) = (k (τ (τ (M.op (σ (σ y)) (σ (σ y))))) (σ y)) := by
    first
    | (have i₁ := eq38689 (τ (M.op (σ sF3) (σ sF3)))
       have i₂ := eq617 sF3
       grind)
    | exact superpose eq617 eq38689
    | exact resolve eq38689 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq40922 : (τ (τ (M.op (M.op x y) y))) = (k (τ (τ (M.op (σ y) (σ y)))) (σ y)) := by
    first
    | exact superpose eq38560 eq40708
    | exact resolve eq40708 eq38560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40708
  have eq40974 : (τ (M.op (M.op x y) y)) = (k (τ (τ (M.op (σ y) (σ y)))) (σ y)) := by
    first
    | exact superpose eq17449 eq40922
    | exact resolve eq40922 eq17449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40922
  have eq40998 : (M.op (M.op x y) y) = (k (τ (τ (M.op (σ y) (σ y)))) (σ y)) := by
    first
    | exact superpose eq17449 eq40974
    | exact resolve eq40974 eq17449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17449 eq40974
  have eq41006 : (M.op (M.op x y) (σ y)) = (k (τ (τ (M.op (σ y) (σ y)))) (σ y)) := by
    first
    | (have i₁ := eq40998
       have i₂ := eq38552
       grind)
    | exact superpose eq38552 eq40998
    | exact resolve eq40998 eq38552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40998
  have eq41380 : (M.op (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18562 eq39226
    | exact resolve eq39226 eq18562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18562 eq39226
  have eq41466 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq41380
       have i₂ := eq38552
       grind)
    | exact superpose eq38552 eq41380
    | exact resolve eq41380 eq38552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41380
  have eq41509 : x = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq41466
       have i₂ := eq38552
       grind)
    | exact superpose eq38552 eq41466
    | exact resolve eq41466 eq38552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41466
  have eq41526 : x = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq38600 eq41509
    | exact resolve eq41509 eq38600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38600 eq41509
  have eq41527 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq41526
  have eq57921 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (σ y) (σ y))) ∨ (M.op x y) = (k x (σ y)) ∨ x = (M.op (σ y) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq38589 eq174
    | exact resolve eq174 eq38589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57940 : (M.op (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (k x (σ y)) ∨ x = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq38589 eq39229
    | exact resolve eq39229 eq38589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57945 : (σ y) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (k x (σ y)) ∨ x = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq38589 eq57940
    | exact resolve eq57940 eq38589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57940
  have eq57959 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op (σ y) (σ y))) ∨ (M.op x y) = (k x (σ y)) ∨ x = (M.op (σ y) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq57921 x x X2
       have i₂ := eq194 x x
       grind)
    | (have i₁ := eq57921 x y X2
       have i₂ := eq194 X2 x
       grind)
    | exact superpose eq194 eq57921
    | (have j0 := eq57921 x y X2
       grind)
    | exact resolve eq57921 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57921
  have eq57991 : ∀ X2 : G, (M.op X2 (M.op (σ y) (σ y))) = (M.op (M.op x y) (σ y)) ∨ (M.op x y) = (k x (σ y)) ∨ x = (M.op (σ y) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq57959 X2
       have i₂ := eq38552
       grind)
    | exact superpose eq38552 eq57959
    | exact resolve eq57959 eq38552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57959
  have eq58019 : ∀ X2 : G, (σ y) = (M.op X2 (M.op (σ y) (σ y))) ∨ (M.op x y) = (k x (σ y)) ∨ x = (M.op (σ y) (σ y)) := by
    intro X2
    first
    | exact superpose eq57945 eq57991
    | exact resolve eq57991 eq57945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57945 eq57991
  have eq58041 : ∀ X2 : G, (σ y) = (M.op X2 (σ y)) ∨ (M.op x y) = (k x (σ y)) ∨ x = (M.op (σ y) (σ y)) := by
    intro X2
    first
    | exact superpose eq38589 eq58019
    | exact resolve eq58019 eq38589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38589 eq58019
  have eq58528 : (M.op x y) = (k x (σ y)) ∨ (M.op x y) = (σ y) ∨ x = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq58041 eq38559
    | exact resolve eq38559 eq58041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58041
  have eq58797 : (τ (M.op x y)) = (k (τ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ x = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq58528 eq38689
    | exact resolve eq38689 eq58528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38689
  have eq58798 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ x = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq58528 eq38562
    | exact resolve eq38562 eq58528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58528
  have eq58805 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ x = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq58798
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq58798
    | exact resolve eq58798 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58798
  have eq58810 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (σ y) ∨ x = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq58805
    | exact resolve eq58805 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58805
  have eq59348 : (σ (σ (M.op x y))) = (k (σ (σ x)) (σ y)) ∨ (M.op x y) = (σ y) ∨ x = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq58810 eq38562
    | exact resolve eq38562 eq58810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38562 eq58810
  have eq59465 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (σ y) (σ y))) ∨ x = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq41527 eq174
    | exact resolve eq174 eq41527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq59484 : (M.op (σ y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq41527 eq39229
    | exact resolve eq39229 eq41527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59490 : (σ y) = (M.op (M.op x y) (σ y)) ∨ x = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq41527 eq59484
    | exact resolve eq59484 eq41527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59484
  have eq59504 : ∀ X2 : G, (M.op (M.op x y) y) = (M.op X2 (M.op (σ y) (σ y))) ∨ x = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq59465 x x X2
       have i₂ := eq194 x x
       grind)
    | (have i₁ := eq59465 x y X2
       have i₂ := eq194 X2 x
       grind)
    | exact superpose eq194 eq59465
    | (have j0 := eq59465 x y X2
       grind)
    | exact resolve eq59465 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq59465
  have eq59536 : ∀ X2 : G, (M.op X2 (M.op (σ y) (σ y))) = (M.op (M.op x y) (σ y)) ∨ x = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    intro X2
    first
    | (have i₁ := eq59504 X2
       have i₂ := eq38552
       grind)
    | exact superpose eq38552 eq59504
    | exact resolve eq59504 eq38552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59504
  have eq59564 : ∀ X2 : G, (M.op X2 (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    intro X2
    first
    | exact superpose eq41527 eq59536
    | exact resolve eq59536 eq41527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41527 eq59536
  have eq59586 : ∀ X2 : G, (σ y) = (M.op X2 (σ y)) ∨ x = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    intro X2
    first
    | exact superpose eq59490 eq59564
    | exact resolve eq59564 eq59490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59490 eq59564
  have eq61216 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq59586 eq38559
    | exact resolve eq38559 eq59586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59586
  have eq61502 : (M.op (M.op x y) (σ y)) = (k (σ (σ x)) (σ y)) ∨ x = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq61216 eq38606
    | exact resolve eq38606 eq61216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38606
  have eq61506 : (M.op (M.op x y) (σ y)) = (k (τ (τ (σ x))) (σ y)) ∨ x = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq61216 eq41006
    | exact resolve eq41006 eq61216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41006
  have eq61546 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq61216 eq39229
    | exact resolve eq39229 eq61216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61547 : x ≠ (σ x) ∨ x = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq61216
  have eq61556 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq26 eq61546
    | exact resolve eq61546 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61546
  have eq61578 : (M.op (M.op x y) (σ y)) = (k (τ x) (σ y)) ∨ x = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq29 eq61506
    | exact resolve eq61506 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq61506
  have eq61579 : (σ (σ (M.op x y))) = (M.op (M.op x y) (σ y)) ∨ x = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq59348 eq61502
    | exact resolve eq61502 eq59348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59348 eq61502
  have eq61607 : (τ (M.op x y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq58797 eq61578
    | exact resolve eq61578 eq58797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58797 eq61578
  have eq61608 : x = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (σ (M.op x y))) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq61556 eq61579
    | exact resolve eq61579 eq61556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61579
  have eq61628 : x = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (τ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq61556 eq61607
    | exact resolve eq61607 eq61556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61607
  have eq61676 : x = (σ x) ∨ (σ y) = (M.op (M.op x y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (σ (M.op x y))) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq61608 eq39994
    | exact resolve eq39994 eq61608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61716 : (M.op (M.op x y) (σ y)) = (M.op x (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (σ (M.op x y))) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq61608 eq39229
    | exact resolve eq39229 eq61608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61608
  have eq61728 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (σ (M.op x y))) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq38559 eq61716
    | exact resolve eq61716 eq38559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61716
  have eq61749 : x = (σ x) ∨ (σ y) = (M.op (M.op x y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (σ (M.op x y))) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq61676
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq61676
    | exact resolve eq61676 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61676
  have eq61775 : x = (σ x) ∨ (M.op x y) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (σ (M.op x y))) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq61728 eq61749
    | exact resolve eq61749 eq61728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61728 eq61749
  have eq61776 : (M.op (σ x) (σ y)) = (σ (σ (M.op x y))) ∨ (M.op x y) = (σ y) ∨ x = (σ x) := by grind
  clear eq61775
  have eq61806 : (σ (M.op x y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ y) ∨ x = (σ x) := by
    first
    | exact superpose eq61776 eq15
    | exact resolve eq15 eq61776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61776
  have eq62771 : (M.op (M.op x y) (σ y)) = (M.op x (σ y)) ∨ (M.op (σ x) (σ y)) = (τ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq61628 eq39229
    | exact resolve eq39229 eq61628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61628
  have eq62783 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ (M.op (σ x) (σ y)) = (τ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq38559 eq62771
    | exact resolve eq62771 eq38559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62771
  have eq64199 : (M.op x y) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (τ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq62783 eq38594
    | exact resolve eq38594 eq62783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62783
  have eq64263 : (M.op (σ x) (σ y)) = (τ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq20 eq64199
    | exact resolve eq64199 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64199
  have eq64290 : (M.op x y) = (σ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq64263 eq14
    | exact resolve eq14 eq64263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64263
  have eq65935 : x = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq61556 eq38595
    | exact resolve eq38595 eq61556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38595
  have eq66758 : x = (σ x) ∨ (σ y) = (M.op (M.op x y) (σ y)) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq65935 eq39994
    | exact resolve eq39994 eq65935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39994 eq65935
  have eq66832 : x = (σ x) ∨ (σ y) = (M.op (M.op x y) (σ y)) ∨ (M.op (σ x) (σ y)) = (τ (M.op (σ x) (σ y))) ∨ (M.op x y) = (σ y) := by
    first
    | (have i₁ := eq66758
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq66758
    | exact resolve eq66758 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq66758
  have eq66858 : x = (σ x) ∨ (σ y) = (M.op (M.op x y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq61806 eq66832
    | exact resolve eq66832 eq61806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61806 eq66832
  have eq66876 : (σ y) = (M.op (M.op x y) (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq66858
       have r₂ := eq27
       grind)
    | exact resolve eq66858 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66858
  have eq66901 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (σ x) ∨ (M.op x y) = (σ y) := by
    intro X0
    first
    | exact superpose eq66876 eq38563
    | exact resolve eq38563 eq66876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66916 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ y) ∨ x = (σ x) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq66876 eq61556
    | exact resolve eq61556 eq66876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61556 eq66876
  have eq66953 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (σ y) (σ y)) ∨ (M.op x y) = (σ y) ∨ x = (σ x) := by grind
  clear eq66916
  have eq66974 : x = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | (have r₁ := eq66953
       have r₂ := eq61547
       grind)
    | exact resolve eq66953 eq61547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61547 eq66953
  have eq67097 : (M.op x y) = (σ y) ∨ x = (σ x) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq66901 eq38559
    | exact resolve eq38559 eq66901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66901
  have eq67185 : (M.op x y) = (σ y) ∨ x = (σ x) := by grind
  clear eq67097
  have eq67275 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq67185 eq26
    | exact resolve eq26 eq67185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67386 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq67185 eq38559
    | exact resolve eq38559 eq67185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67387 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq67185 eq38560
    | exact resolve eq38560 eq67185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67390 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (M.op (M.op x y) (M.op x y))) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq67185 eq38563
    | exact resolve eq38563 eq67185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38563
  have eq67500 : (M.op x y) = (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq20 eq67387
    | exact resolve eq67387 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67387
  have eq67501 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (σ x) := by
    first
    | exact superpose eq191 eq67386
    | exact resolve eq67386 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq67386
  have eq67602 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ x = (σ x) := by
    first
    | (have i₁ := eq67501
       have i₂ := eq38552
       grind)
    | exact superpose eq38552 eq67501
    | exact resolve eq67501 eq38552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38552 eq67501
  have eq67678 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq67185 eq67602
    | exact resolve eq67602 eq67185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67185 eq67602
  have eq68761 : (M.op (M.op x y) (σ y)) = (M.op x (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq66974 eq39229
    | exact resolve eq39229 eq66974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39229 eq66974
  have eq68780 : (M.op x y) = (M.op (M.op x y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq38559 eq68761
    | exact resolve eq68761 eq38559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68761
  have eq68972 : (M.op x y) = (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq68780 eq38594
    | exact resolve eq38594 eq68780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38594 eq68780
  have eq69045 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq20 eq68972
    | exact resolve eq68972 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68972
  have eq69110 : (M.op x y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq69045 eq64290
    | exact resolve eq64290 eq69045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64290 eq69045
  have eq69114 : (M.op x y) = (σ (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by grind
  clear eq69110
  have eq69138 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ y) := by
    first
    | exact superpose eq38560 eq69114
    | exact resolve eq69114 eq38560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69114
  have eq69139 : (M.op x y) = (σ y) ∨ (M.op x y) = (σ (M.op x y)) := by grind
  clear eq69138
  have eq69263 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq69139 eq38560
    | exact resolve eq38560 eq69139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38560 eq69139
  have eq69412 : (M.op x y) = (σ (M.op x y)) ∨ (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq69263
    | exact resolve eq69263 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq69263
  have eq69413 : (M.op x y) = (σ (M.op x y)) := by grind
  clear eq69412
  have eq77403 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (σ x) ∨ x = (σ x) := by
    intro X0
    first
    | exact superpose eq67678 eq67390
    | exact resolve eq67390 eq67678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67390 eq67678
  have eq77551 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op x y)) ∨ x = (σ x) := by
    intro X0
    first
    | (have j0 := eq77403 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77403
  have eq77785 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq77551 eq67275
    | exact resolve eq67275 eq77551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67275 eq77551
  have eq77792 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) := by grind
  clear eq77785
  have eq77965 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) := by
    first
    | exact superpose eq77792 eq27
    | exact resolve eq27 eq77792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77792
  have eq78015 : x = (σ x) := by
    first
    | (have r₁ := eq77965
       have r₂ := eq67500
       grind)
    | exact resolve eq77965 eq67500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67500 eq77965
  have eq78063 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq38559
       have i₂ := eq78015
       grind)
    | exact superpose eq78015 eq38559
    | exact resolve eq38559 eq78015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38559 eq78015
  have eq78618 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq78063 eq26
    | exact resolve eq26 eq78063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq78063
  have eq78662 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq78618 eq27
    | exact resolve eq27 eq78618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq78618
  have eq78709 : False := by grind
  exact eq78709

/-- `Equation4452`: `x ◇ (y ◇ x) = (z ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pxy_pxx_pxy_Equation4452 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4452 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4452.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) X0) := by
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
  have eq52 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X3 X1) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X1 x X3
       have i₂ := eq14 X1 x X0
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op y (M.op X0 y)) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq14 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y X0 x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op X0 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X0 X1 x
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X2 X1) ∨ (k (M.op X2 X1) X1) = (M.op (M.op X2 X1) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X2 X1) X1
       have i₂ := eq14 X1 X2 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op X2 X1) X1
       grind)
    | (have r₁ := eq13 (M.op (M.op X2 X0) X0) X0
       have r₂ := eq14 X0 (M.op X2 X0) X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : y ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq70 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
    intro X0
    first
    | (have i₁ := eq36 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36
    | exact resolve eq36 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq80 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq85 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq44
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq44 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq104
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq104
    | exact resolve eq104 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq112
    | exact resolve eq112 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq126 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq144 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq133 eq16
    | exact resolve eq16 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : (M.op (M.op x y) y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq55 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq55
    | (have j0 := eq55 x
       grind)
    | exact resolve eq55 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq219 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq56
    | (have j0 := eq56 (σ x)
       grind)
    | exact resolve eq56 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq277 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq34
  have eq447 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) ≠ (M.op X2 X1) ∨ (M.op (M.op X0 X1) X1) = X1 ∨ (k X1 (M.op X2 X1)) = (M.op X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op X0 X1)
       have i₂ := eq52 X0 X1 x
       grind)
    | (have i₁ := eq12 X1 (M.op x X1)
       have i₂ := eq52 X0 X1 x
       grind)
    | exact superpose eq52 eq12
    | (have j0 := eq12 X1 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op x X1) X1)
       have r₂ := eq52 (M.op x X1) X1 x
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op X0 X1) X1)
       have r₂ := eq52 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq12 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1665 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq114 eq80
    | (have j0 := eq80 (σ x) (σ y)
       grind)
    | exact resolve eq80 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq1666 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq1665
    | exact resolve eq1665 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1665
  have eq1669 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq1666
       have r₂ := eq27
       grind)
    | exact resolve eq1666 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1666
  have eq1682 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1669 eq57
    | exact resolve eq57 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1690 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq26 eq1682
    | (have j0 := eq1682 X0
       grind)
    | exact resolve eq1682 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1682
  have eq1870 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1690 x
       have i₂ := eq14 sF2 x x
       grind)
    | exact superpose eq14 eq1690
    | exact resolve eq1690 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1690
  have eq1909 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1669 eq1870
    | exact resolve eq1870 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1870
  have eq1950 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq1909
  have eq1972 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1950 eq1669
    | exact resolve eq1669 eq1950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1950
  have eq1994 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1972
  have eq2008 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq57 x X0 y
       have i₂ := eq1994
       grind)
    | exact superpose eq1994 eq57
    | exact resolve eq57 eq1994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2018 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2008 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2008
    | (have j0 := eq2008 X0
       grind)
    | exact resolve eq2008 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2008
  have eq2234 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2018 x
       have i₂ := eq14 x x X0
       grind)
    | exact superpose eq14 eq2018
    | exact resolve eq2018 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2018
  have eq2268 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2234 (M.op x x)
       have i₂ := eq2234 x
       grind)
    | exact superpose eq2234 eq2234
    | exact resolve eq2234 eq2234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2276 : (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2234 y
       have i₂ := eq1994
       grind)
    | exact superpose eq1994 eq2234
    | exact resolve eq2234 eq1994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2309 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op X0 x) x) ∨ (M.op (M.op x y) x) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq67 X0 x (M.op X0 x)
       have i₂ := eq2234 X0
       grind)
    | exact superpose eq2234 eq67
    | exact resolve eq67 eq2234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq2319 : (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2276
  have eq2320 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2268
  have eq2322 : (M.op (M.op x y) x) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq2309 x
       have r₂ := eq2234 x
       grind)
    | exact resolve eq2309 eq2234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2234 eq2309
  have eq2342 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1994
       have i₂ := eq2319
       grind)
    | exact superpose eq2319 eq1994
    | exact resolve eq1994 eq2319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1994 eq2319
  have eq2365 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2342
  have eq2369 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2365 eq70
    | (have r₁ := eq70
       have r₂ := eq2365
       grind)
    | exact resolve eq70 eq2365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq2365
  have eq2375 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq2369
  have eq2403 : (k (σ (M.op x y)) (σ x)) = (σ (M.op (M.op x y) x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2322 eq133
    | exact resolve eq133 eq2322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq2322
  have eq2404 : (k y x) = (τ (M.op (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2375 eq85
    | exact resolve eq85 eq2375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq2375
  have eq2430 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2320 eq2403
    | exact resolve eq2403 eq2320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2320 eq2403
  have eq2444 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2430
  have eq2446 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq2444
    | exact resolve eq2444 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2444
  have eq2448 : (τ (σ (M.op x y))) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2446 eq144
    | exact resolve eq144 eq2446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2446
  have eq2450 : (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq2448
    | exact resolve eq2448 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2448
  have eq2460 : (τ (σ y)) = (k y x) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1669 eq2404
    | exact resolve eq2404 eq1669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669 eq2404
  have eq2474 : y = (k y x) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq2460
    | exact resolve eq2460 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2460
  have eq7832 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq80 y x
       have i₂ := eq2474
       grind)
    | exact superpose eq2474 eq80
    | (have j0 := eq80 x y
       grind)
    | exact resolve eq80 eq2474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2474
  have eq7833 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq7832
  have eq7835 : y = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7833
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7833
    | exact resolve eq7833 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7833
  have eq7864 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq57 x X0 y
       have i₂ := eq7835
       grind)
    | exact superpose eq7835 eq57
    | exact resolve eq57 eq7835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7898 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7864 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7864
    | (have j0 := eq7864 X0
       grind)
    | exact resolve eq7864 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7864
  have eq8248 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7898 x
       have i₂ := eq14 x x X0
       grind)
    | exact superpose eq14 eq7898
    | exact resolve eq7898 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7898
  have eq8421 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq8248 y
       have i₂ := eq7835
       grind)
    | exact superpose eq7835 eq8248
    | exact resolve eq8248 eq7835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8248
  have eq8505 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq8421
  have eq8562 : y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7835
       have i₂ := eq8505
       grind)
    | exact superpose eq8505 eq7835
    | exact resolve eq7835 eq8505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7835 eq8505
  have eq8606 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq8562
  have eq8764 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8606 eq20
    | exact resolve eq20 eq8606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8766 : y ≠ y ∨ (k y x) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8606 eq69
    | (have r₁ := eq69
       have r₂ := eq8606
       grind)
    | exact resolve eq69 eq8606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq8768 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8606 eq126
    | exact resolve eq126 eq8606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq8792 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8606 eq2450
    | exact resolve eq2450 eq8606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2450
  have eq8814 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq8815 : (k y x) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq8766
  have eq8848 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq8768 X0
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq8768
    | exact resolve eq8768 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq8768
  have eq8851 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8764
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq8764
    | exact resolve eq8764 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8764
  have eq9168 : ∀ X0 : G, (k (τ (σ y)) X0) = (τ (k (σ (M.op x y)) (σ X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq8848 eq277
    | exact resolve eq277 eq8848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8848
  have eq9195 : ∀ X0 : G, (k (τ (σ (M.op x y))) X0) = (k (τ (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9168 x
       have i₂ := eq277 sF1 x
       grind)
    | exact superpose eq277 eq9168
    | exact resolve eq9168 eq277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277 eq9168
  have eq9200 : ∀ X0 : G, (k y X0) = (k (τ (σ (M.op x y))) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq9195
    | exact resolve eq9195 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq9195
  have eq9203 : ∀ X0 : G, (k y X0) = (k (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30 eq9200
    | exact resolve eq9200 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9200
  have eq9916 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq8792
       grind)
    | exact superpose eq8792 eq77
    | exact resolve eq77 eq8792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8792
  have eq9920 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9916
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq9916
    | exact resolve eq9916 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9916
  have eq10117 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8851 eq9920
    | exact resolve eq9920 eq8851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9920
  have eq10133 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10117
  have eq10137 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10133
       have r₂ := eq27
       grind)
    | exact resolve eq10133 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10133
  have eq10141 : (τ (σ (M.op x y))) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10137 eq144
    | exact resolve eq144 eq10137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144 eq10137
  have eq10143 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq10141
    | exact resolve eq10141 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq10141
  have eq10144 : y = (k y x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq8606 eq10143
    | exact resolve eq10143 eq8606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10160 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10143 eq9203
    | exact resolve eq9203 eq10143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9203 eq10143
  have eq10162 : (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq10160
  have eq10169 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10144
       have r₂ := eq8814
       grind)
    | exact resolve eq10144 eq8814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8814 eq10144
  have eq10175 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq10162
       grind)
    | exact superpose eq10162 eq77
    | exact resolve eq77 eq10162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10179 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8815
       have i₂ := eq10162
       grind)
    | exact superpose eq10162 eq8815
    | exact resolve eq8815 eq10162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10162
  have eq10181 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq10179
  have eq10189 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq10175
    | exact resolve eq10175 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10175
  have eq10196 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq77
       have i₂ := eq10169
       grind)
    | exact superpose eq10169 eq77
    | exact resolve eq77 eq10169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq10197 : y = (M.op y x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq8815
       have i₂ := eq10169
       grind)
    | exact superpose eq10169 eq8815
    | exact resolve eq8815 eq10169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8815 eq10169
  have eq10203 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq10197
  have eq10209 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10196
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10196
    | exact resolve eq10196 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq10196
  have eq10402 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq10181
       grind)
    | exact superpose eq10181 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq10181
       grind)
    | exact resolve eq12 eq10181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10181
  have eq10431 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ (k x y) = (M.op x x) := by grind
  clear eq10402
  have eq10439 : (k x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq10431
       have r₂ := eq8606
       grind)
    | exact resolve eq10431 eq8606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8606 eq10431
  have eq10625 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10189 eq80
    | (have j0 := eq80 (σ y) (σ x)
       grind)
    | exact resolve eq80 eq10189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10189
  have eq10633 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10625
    | exact resolve eq10625 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10625
  have eq10669 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq57 x X0 y
       have i₂ := eq10203
       grind)
    | exact superpose eq10203 eq57
    | exact resolve eq57 eq10203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10203
  have eq10709 : ∀ X0 : G, (M.op x y) = (M.op x (M.op X0 x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10669 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10669
    | (have j0 := eq10669 X0
       grind)
    | exact resolve eq10669 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10669
  have eq10739 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10209 eq80
    | (have j0 := eq80 (σ x) (σ y)
       grind)
    | exact resolve eq80 eq10209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10209
  have eq10747 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq10739
    | exact resolve eq10739 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10739
  have eq12935 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10709 x
       have i₂ := eq14 x x X0
       grind)
    | exact superpose eq14 eq10709
    | exact resolve eq10709 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10709
  have eq13742 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq8851 eq10633
    | exact resolve eq10633 eq8851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8851
  have eq13786 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq13742
  have eq13809 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10747 eq57
    | exact resolve eq57 eq10747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10747
  have eq13856 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq13809
    | (have j0 := eq13809 X0
       grind)
    | exact resolve eq13809 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13809
  have eq62811 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13856 x
       have i₂ := eq14 sF2 x x
       grind)
    | exact superpose eq14 eq13856
    | exact resolve eq13856 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13856
  have eq63709 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10633 eq62811
    | exact resolve eq62811 eq10633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10633 eq62811
  have eq63908 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq63709
  have eq64032 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq63908 eq13786
    | exact resolve eq13786 eq63908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13786 eq63908
  have eq64153 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq64032
  have eq64158 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq64153
       have r₂ := eq27
       grind)
    | exact resolve eq64153 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64153
  have eq64165 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq64158 eq219
    | exact resolve eq219 eq64158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq64204 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq64165
    | exact resolve eq64165 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64165
  have eq65337 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq64204 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq64204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64204
  have eq65457 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq65337
       have r₂ := eq64158
       grind)
    | exact resolve eq65337 eq64158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65337
  have eq65458 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq65457
    | exact resolve eq65457 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65457
  have eq66751 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq65458 eq61
    | exact resolve eq61 eq65458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq65458
  have eq67943 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10439
       have i₂ := eq66751
       grind)
    | exact superpose eq66751 eq10439
    | exact resolve eq10439 eq66751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10439 eq66751
  have eq67948 : (M.op x x) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq67943
  have eq69195 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12935 x
       have i₂ := eq67948
       grind)
    | exact superpose eq67948 eq12935
    | exact resolve eq12935 eq67948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12935
  have eq69313 : (M.op x y) = (M.op (τ (M.op (σ x) (σ y))) x) ∨ x = (M.op x y) := by grind
  clear eq69195
  have eq69328 : (M.op x y) = (M.op (τ (σ x)) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq64158 eq69313
    | exact resolve eq69313 eq64158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69313
  have eq69480 : (M.op x y) = (M.op (τ (σ x)) x) ∨ x = (M.op x y) := by grind
  clear eq69328
  have eq69483 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq69480
    | exact resolve eq69480 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69480
  have eq69486 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq67948
       have i₂ := eq69483
       grind)
    | exact superpose eq69483 eq67948
    | exact resolve eq67948 eq69483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67948 eq69483
  have eq69635 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq69486
  have eq71016 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq64158 eq69635
    | exact resolve eq69635 eq64158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64158 eq69635
  have eq71047 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by grind
  clear eq71016
  have eq71052 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq71047
    | exact resolve eq71047 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq71047
  have eq71053 : x = (M.op x y) := by grind
  clear eq71052
  have eq71056 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq71053 eq20
    | exact resolve eq20 eq71053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq71065 : (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq71053 eq211
    | exact resolve eq211 eq71053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq71123 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq71065
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq71065
    | exact resolve eq71065 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71065
  have eq71130 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq71056
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq71056
    | exact resolve eq71056 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71056
  have eq71131 : x = (M.op y x) := by
    first
    | exact superpose eq71053 eq71123
    | exact resolve eq71123 eq71053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71123
  have eq72595 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq71130 eq26
    | exact resolve eq26 eq71130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq72712 : x ≠ x ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq71131
       grind)
    | exact superpose eq71131 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq71131
       grind)
    | exact resolve eq13 eq71131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71131
  have eq72830 : (M.op x y) = (k x y) := by grind
  clear eq72712
  have eq72835 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq72830
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq72830
    | exact resolve eq72830 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq72830
  have eq72841 : x = (k x y) := by
    first
    | exact superpose eq71053 eq72835
    | exact resolve eq72835 eq71053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71053 eq72835
  have eq73627 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq72841
       grind)
    | exact superpose eq72841 eq44
    | exact resolve eq44 eq72841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq72841
  have eq73632 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq71130 eq73627
    | exact resolve eq73627 eq71130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73627
  have eq73635 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq73632
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq73632
    | exact resolve eq73632 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq73632
  have eq73637 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq71130 eq73635
    | exact resolve eq73635 eq71130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71130 eq73635
  have eq73654 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq73637 eq80
    | (have j0 := eq80 (σ y) (σ (M.op x y))
       grind)
    | exact resolve eq80 eq73637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq73656 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq72595 eq73654
    | exact resolve eq73654 eq72595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73654
  have eq73659 : (σ y) = (M.op (σ y) (σ (M.op x y))) := by
    first
    | (have r₁ := eq73656
       have r₂ := eq27
       grind)
    | exact resolve eq73656 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73656
  have eq73669 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ (M.op x y)) (σ y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq73659 eq13
    | (have j0 := eq13 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq13 eq73659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73674 : ∀ X0 : G, (M.op (σ y) (σ (M.op x y))) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq73659 eq52
    | exact resolve eq52 eq73659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq73679 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq73659 eq57
    | exact resolve eq57 eq73659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq73886 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq72595 eq73679
    | exact resolve eq73679 eq72595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73679
  have eq73891 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq73659 eq73674
    | exact resolve eq73674 eq73659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73659 eq73674
  have eq73896 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq73637 eq73669
    | exact resolve eq73669 eq73637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73669
  have eq73918 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq72595 eq73896
    | exact resolve eq73896 eq72595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72595 eq73896
  have eq73922 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have r₁ := eq73918
       have r₂ := eq27
       grind)
    | exact resolve eq73918 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73918
  have eq75612 : ∀ X0 : G, (σ y) ≠ (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq73891 eq447
    | (have j0 := eq447 X0 (σ (M.op x y)) x
       grind)
    | exact resolve eq447 eq73891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq447
  have eq75865 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ (M.op x y))) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq75612 X0
       grind)
    | (have r₁ := eq75612 X0
       have r₂ := eq73891 X0
       grind)
    | exact resolve eq75612 eq73891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75612
  have eq76033 : (σ (M.op x y)) = (σ y) ∨ (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq73891 eq75865
    | exact resolve eq75865 eq73891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73891 eq75865
  have eq76154 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have r₁ := eq76033
       have r₂ := eq73922
       grind)
    | exact resolve eq76033 eq73922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73922 eq76033
  have eq76227 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq73637 eq76154
    | exact resolve eq76154 eq73637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73637 eq76154
  have eq76279 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq76227 eq73886
    | exact resolve eq73886 eq76227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73886
  have eq76441 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq76227 eq76279
    | exact resolve eq76279 eq76227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76227 eq76279
  have eq76473 : False := by grind
  exact eq76473

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X0) := by
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
  have eq67 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
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
       have i₂ := eq67 (σ X0)
       grind)
    | exact superpose eq67 eq15
    | exact resolve eq15 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq71
    | exact resolve eq71 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq71
  have eq96 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq615 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq638 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq615 X0 X1
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq615
    | (have j0 := eq615 X0 X1
       grind)
    | exact resolve eq615 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq1802 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq638 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq638
    | exact resolve eq638 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638
  have eq1852 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1802 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq1802
    | (have j0 := eq1802 X0 X1
       grind)
    | exact resolve eq1802 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1802
  have eq1866 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1852 X0 X1
       have j1 := eq96 X1 X0
       grind)
    | (have r₁ := eq1852 X1 X0
       have r₂ := eq96 X0 X1
       grind)
    | (have r₁ := eq1852 (M.op X1 (σ X0)) (M.op X0 X0)
       have r₂ := eq96 X0 X1
       grind)
    | exact resolve eq1852 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq1852
  have eq1877 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1866 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1866
    | exact resolve eq1866 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1888 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1866 (σ X1) X0
       grind)
    | exact superpose eq1866 eq15
    | (have j1 := eq1866 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq1866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1866
  have eq1927 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq1877 X0 (τ X1)
       grind)
    | exact superpose eq1877 eq19
    | (have j1 := eq1877 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq1877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1877
  have eq2204 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1927 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1927
    | exact resolve eq1927 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1927
  have eq2279 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2204 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2204
    | (have j0 := eq2204 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq2204 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2204
  have eq2528 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1888 x y
       grind)
    | exact superpose eq1888 eq16
    | (have j1 := eq1888 x y
       grind)
    | exact resolve eq16 eq1888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888
  have eq2561 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2528
       have i₂ := eq2279 y x
       grind)
    | exact superpose eq2279 eq2528
    | (have j1 := eq2279 (σ x) (σ y)
       grind)
    | (have r₁ := eq2528
       have r₂ := eq2279 y x
       grind)
    | (have r₁ := eq2528
       have r₂ := eq2279 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2528
       have r₂ := eq2279 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2528 eq2279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2279 eq2528
  have eq2562 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq2561
  have eq2565 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2562
       grind)
    | exact superpose eq2562 eq16
    | exact resolve eq16 eq2562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2562
  have eq2566 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq2565
       have r₂ := eq82 x
       grind)
    | exact resolve eq2565 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2565
  have eq2567 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2566
       grind)
    | exact superpose eq2566 eq16
    | exact resolve eq16 eq2566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2568 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2566
       grind)
    | exact superpose eq2566 eq10
    | exact resolve eq10 eq2566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2566
  have eq2626 : x = y := by
    first
    | (have i₁ := eq2568
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2568
    | exact resolve eq2568 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2568
  have eq2627 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2567
       have i₂ := eq82 x
       grind)
    | exact superpose eq82 eq2567
    | exact resolve eq2567 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq2567
  have eq2628 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq2627
       have i₂ := eq2626
       grind)
    | exact superpose eq2626 eq2627
    | exact resolve eq2627 eq2626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2626 eq2627
  have eq2629 : False := by grind
  exact eq2629

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxx_pyy_pxy_pyx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) ≠ (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq33 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq12 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq33 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq88 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq71 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq71
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq88 X0
       have i₂ := eq17 X0 (τ X0)
       grind)
    | exact superpose eq17 eq88
    | exact resolve eq88 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq96 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq95 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq95
    | exact resolve eq95 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq117 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq96 (τ X0)
       grind)
    | exact superpose eq96 eq18
    | exact resolve eq18 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq125 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq124 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq124
    | exact resolve eq124 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq130 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq125 X0
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq125
    | exact resolve eq125 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq215 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq117 (σ X0) (σ X1)
       grind)
    | exact superpose eq117 eq15
    | (have j1 := eq117 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq215 X0 X1
       have i₂ := eq71 X1
       grind)
    | exact superpose eq71 eq215
    | (have j0 := eq215 X0 X1
       grind)
    | exact resolve eq215 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq242 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq229 X0 X1
       have i₂ := eq96 X1
       grind)
    | exact superpose eq96 eq229
    | (have j0 := eq229 X0 X1
       grind)
    | exact resolve eq229 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq250 : ∀ X0 X1 : G, (σ (k X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq242 X0 X1
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq242
    | (have j0 := eq242 X0 X1
       grind)
    | exact resolve eq242 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq252 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq250 X0 X1
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq250
    | (have j0 := eq250 X0 X1
       grind)
    | exact resolve eq250 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq430 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq252 x y
       grind)
    | exact superpose eq252 eq16
    | (have j1 := eq252 x y
       grind)
    | exact resolve eq16 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq439 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq430
       grind)
    | exact superpose eq430 eq10
    | exact resolve eq10 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq470 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq439
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq439
    | exact resolve eq439 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq807 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 X1
       have i₂ := eq71 X1
       grind)
    | exact superpose eq71 eq39
    | (have j0 := eq39 X0 X1
       grind)
    | exact resolve eq39 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq808 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq807 X0 X1
       have i₂ := eq96 X1
       grind)
    | exact superpose eq96 eq807
    | (have j0 := eq807 X0 X1
       grind)
    | exact resolve eq807 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq809 : ∀ X0 X1 : G, (σ (k X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq808 X0 X1
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq808
    | (have j0 := eq808 X0 X1
       grind)
    | exact resolve eq808 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq808
  have eq810 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq809 X0 X1
       have i₂ := eq96 X0
       grind)
    | exact superpose eq96 eq809
    | (have j0 := eq809 X0 X1
       grind)
    | exact resolve eq809 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq809
  have eq1002 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq810 X0 X1
       grind)
    | (have i₁ := eq33 X1 X0
       have i₂ := eq810 X0 X1
       grind)
    | exact superpose eq810 eq33
    | (have j1 := eq810 X1 X0
       grind)
    | (have r₁ := eq33 X0 X1
       have r₂ := eq810 X0 X1
       grind)
    | (have r₁ := eq33 X1 X0
       have r₂ := eq810 X0 X1
       grind)
    | exact resolve eq33 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq810
  have eq1019 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1002 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1002
  have eq1020 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1019 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq1058 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1020 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1020
    | (have j0 := eq1020 (τ X0) X1
       grind)
    | exact resolve eq1020 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1074 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) ≠ (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1020 x y
       grind)
    | exact superpose eq1020 eq16
    | (have j1 := eq1020 x y
       grind)
    | exact resolve eq16 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1118 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1058 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq1058
    | (have j0 := eq1058 X0 X1
       grind)
    | exact resolve eq1058 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1058
  have eq1126 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1118 X0 X1
       have i₂ := eq130 X0
       grind)
    | exact superpose eq130 eq1118
    | (have j0 := eq1118 X0 X1
       grind)
    | exact resolve eq1118 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1118
  have eq1753 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq470
       have i₂ := eq117 x y
       grind)
    | exact superpose eq117 eq470
    | (have j1 := eq117 x y
       grind)
    | exact resolve eq470 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq470
  have eq1759 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq1753
  have eq1760 : (M.op x x) = (M.op y y) := by grind
  clear eq1759
  have eq1775 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X1) ≠ (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1126 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1126
    | (have j0 := eq1126 X1 (τ X0)
       grind)
    | exact resolve eq1126 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq1837 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1775 X0 X1
       have i₂ := eq130 X0
       grind)
    | exact superpose eq130 eq1775
    | (have j0 := eq1775 X0 X1
       grind)
    | (have r₁ := eq1775 X0 X0
       have r₂ := eq130 X0
       grind)
    | exact resolve eq1775 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq1775
  have eq2045 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq1074
       have i₂ := eq1760
       grind)
    | exact superpose eq1760 eq1074
    | exact resolve eq1074 eq1760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1074
  have eq2046 : (σ (M.op x y)) ≠ (σ (k y x)) := by grind
  clear eq2045
  have eq4065 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x x) ≠ (M.op y y) := by
    first
    | (have i₁ := eq2046
       have i₂ := eq1837 x y
       grind)
    | exact superpose eq1837 eq2046
    | (have j1 := eq1837 x y
       grind)
    | exact resolve eq2046 eq1837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1837 eq2046
  have eq4066 : (M.op x x) ≠ (M.op y y) := by grind
  clear eq4065
  have eq4067 : False := by grind
  exact eq4067

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxy_x_pxy_x_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 (M.op X0 X0)) X2 X0
       have i₂ := eq9 X0 (M.op X1 (M.op X0 X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56
    | (have j0 := eq56 (σ X0) (σ X1)
       grind)
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq56 X0 (τ X1)
       grind)
    | exact superpose eq56 eq18
    | (have j1 := eq56 X0 (τ X1)
       grind)
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq33 (τ X0)
       grind)
    | exact superpose eq33 eq18
    | exact resolve eq18 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq83 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq83
    | exact resolve eq83 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq83
  have eq95 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91
    | exact resolve eq91 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) = (M.op (M.op X2 (M.op (M.op X3 X1) (M.op X3 X1))) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 (M.op X3 X1) X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq23 X1 X0 X3
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op X0 (M.op X1 X1)) ∨ (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X0 (M.op X1 X1)) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 (M.op X0 X0)) (M.op X2 X0)
       have i₂ := eq23 X0 X1 X2
       grind)
    | exact superpose eq23 eq13
    | (have j0 := eq13 (M.op X0 (M.op X1 X1)) (M.op X2 X1)
       grind)
    | (have r₁ := eq13 (M.op X1 (M.op X0 X0)) (M.op X2 X0)
       have r₂ := eq23 X0 X1 X2
       grind)
    | exact resolve eq13 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) ≠ (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X0 (M.op X1 X1)) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op X0 X0)) (M.op X2 X0)
       have i₂ := eq23 X0 X1 X2
       grind)
    | exact superpose eq23 eq12
    | exact resolve eq12 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq120 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op (M.op X2 X1) (M.op X0 (M.op X1 X1))) ∨ (M.op X0 (M.op X1 X1)) = (k (M.op X0 (M.op X1 X1)) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq117 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq139 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67 x y
       grind)
    | exact superpose eq67 eq16
    | (have j1 := eq67 x y
       grind)
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq166 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op X1 (M.op X2 (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq9
    | exact resolve eq9 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq344 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq73
    | exact resolve eq73 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq370 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq344 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq344
    | (have j0 := eq344 X0 X1
       grind)
    | exact resolve eq344 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq492 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq139
       have i₂ := eq56 x y
       grind)
    | exact superpose eq56 eq139
    | (have j1 := eq56 (σ x) (σ y)
       grind)
    | exact resolve eq139 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq493 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq492
  have eq1524 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X0 (M.op X1 X1)) (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq120 X0 X1 X2
       have j1 := eq119 X0 X1 X2
       grind)
    | (have r₁ := eq120 X0 X1 X2
       have r₂ := eq119 X0 X1 X2
       grind)
    | exact resolve eq120 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq120
  have eq1535 : ∀ X0 X1 X2 : G, (σ X0) = (k (σ X0) (M.op X2 (M.op X1 (σ (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1524 (σ X0) (M.op X2 (σ (M.op X0 X0))) X2
       have i₂ := eq166 X0 (M.op X2 (σ (M.op X0 X0))) X2
       grind)
    | exact superpose eq166 eq1524
    | exact resolve eq1524 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq1524
  have eq1595 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k (σ (τ X0)) (M.op X1 (M.op X2 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1535 (τ X0) X2 X1
       have i₂ := eq91 X0
       grind)
    | exact superpose eq91 eq1535
    | exact resolve eq1535 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq1535
  have eq1626 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 (M.op X0 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1595 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1595
    | exact resolve eq1595 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1595
  have eq1654 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1626 X2 (M.op X0 (M.op (M.op X1 X2) (M.op X1 X2))) x
       have i₂ := eq114 x X2 X0 X1
       grind)
    | exact superpose eq114 eq1626
    | exact resolve eq1626 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq2070 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) (M.op X2 X0)))) = X0 ∨ (M.op X0 (M.op X1 (M.op (M.op X2 X0) (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X0 (M.op X1 (M.op (M.op X2 X0) (M.op X2 X0)))
       have i₂ := eq1654 X1 X2 X0
       grind)
    | exact superpose eq1654 eq56
    | (have j0 := eq56 X0 (M.op X1 (M.op (M.op X2 X0) (M.op X2 X0)))
       grind)
    | exact resolve eq56 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1654
  have eq2079 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq2070 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070
  have eq2728 : ∀ X0 X1 : G, (M.op X1 X0) = (k (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1626 (M.op X1 X0) X0 x
       have i₂ := eq2079 X0 x X1
       grind)
    | exact superpose eq2079 eq1626
    | exact resolve eq1626 eq2079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626 eq2079
  have eq2857 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq148 (M.op X0 X1) X1
       have i₂ := eq2728 X1 X0
       grind)
    | exact superpose eq2728 eq148
    | (have j0 := eq148 (M.op X0 X1) X1
       grind)
    | exact resolve eq148 eq2728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq2871 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2857 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2857
  have eq3049 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2871 x y
       have i₂ := eq493
       grind)
    | exact superpose eq493 eq2871
    | exact resolve eq2871 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493 eq2871
  have eq3086 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3049
  have eq3246 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3086
       grind)
    | exact superpose eq3086 eq16
    | exact resolve eq16 eq3086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3257 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq2728 (σ y) (σ x)
       have i₂ := eq3086
       grind)
    | exact superpose eq3086 eq2728
    | exact resolve eq2728 eq3086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2728 eq3086
  have eq3260 : (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq3257
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq3257
    | exact resolve eq3257 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3257
  have eq3281 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq370 y x
       have i₂ := eq3260
       grind)
    | exact superpose eq3260 eq370
    | (have j0 := eq370 y x
       grind)
    | exact resolve eq370 eq3260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370 eq3260
  have eq3332 : x = (M.op x y) := by
    first
    | (have r₁ := eq3281
       have r₂ := eq3246
       grind)
    | exact resolve eq3281 eq3246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3281
  have eq3349 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3246
       have i₂ := eq3332
       grind)
    | exact superpose eq3332 eq3246
    | exact resolve eq3246 eq3332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3246 eq3332
  have eq3362 : False := by grind
  exact eq3362

/-- `Equation446`: `x = x ◇ (y ◇ (z ◇ (x ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_x_y_pxy_pxx_pxy_Equation446 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law446 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law446.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
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
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq15
    | exact resolve eq15 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq71
    | exact resolve eq71 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq71
  have eq558 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq608 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq561 x y
       grind)
    | exact superpose eq561 eq16
    | (have j1 := eq561 x y
       grind)
    | exact resolve eq16 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq615 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq561 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2543 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq558 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq558
    | exact resolve eq558 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq2598 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2543 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2543
    | (have j0 := eq2543 X0 X1
       grind)
    | exact resolve eq2543 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2543
  have eq16286 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq608
       have i₂ := eq2598 y x
       grind)
    | exact superpose eq2598 eq608
    | (have j1 := eq2598 (σ x) (σ y)
       grind)
    | (have r₁ := eq608
       have r₂ := eq2598 y x
       grind)
    | (have r₁ := eq608
       have r₂ := eq2598 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq608
       have r₂ := eq2598 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq608 eq2598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2598
  have eq16287 : x = y ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq16286
  have eq20875 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq615 X1 X0
       have i₂ := eq561 X0 X1
       grind)
    | exact superpose eq561 eq615
    | (have j0 := eq615 X0 X1
       have j1 := eq561 X0 X1
       grind)
    | (have r₁ := eq615 X0 X0
       have r₂ := eq561 X0 X0
       grind)
    | exact resolve eq615 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq20880 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq20875 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20875
  have eq20884 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq20880 X0 X1
       have j1 := eq615 X0 X1
       grind)
    | (have r₁ := eq20880 X0 X1
       have r₂ := eq615 (k X0 X1) (k X1 X0)
       grind)
    | (have r₁ := eq20880 X0 X1
       have r₂ := eq615 (k X1 X0) (k X0 X1)
       grind)
    | (have r₁ := eq20880 X0 X1
       have r₂ := eq615 X0 X1
       grind)
    | exact resolve eq20880 eq615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615 eq20880
  have eq64012 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (k (τ X1) (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq20884 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq20884
    | (have j0 := eq20884 (τ X0) (τ X1)
       grind)
    | exact resolve eq20884 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq20884
  have eq64169 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (k (σ (τ X1)) X0) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq64012 X0 X1
       have i₂ := eq19 X0 (τ X1)
       grind)
    | exact superpose eq19 eq64012
    | (have j0 := eq64012 X0 X1
       grind)
    | exact resolve eq64012 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq64012
  have eq64369 : ∀ X0 X1 : G, (k X1 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq64169 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq64169
    | (have j0 := eq64169 X0 X1
       grind)
    | exact resolve eq64169 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64169
  have eq64527 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X0)) = (σ (τ X1)) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq64369 X1 X0
       have i₂ := eq11 (k X1 X0)
       grind)
    | exact superpose eq11 eq64369
    | (have j0 := eq64369 X0 X1
       grind)
    | (have r₁ := eq64369 X1 X1
       have r₂ := eq11 (k X1 X1)
       grind)
    | exact resolve eq64369 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64369
  have eq64662 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (k X0 X1) ≠ (k X1 X0) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq64527 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq64527
    | (have j0 := eq64527 X0 X1
       grind)
    | exact resolve eq64527 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64527
  have eq64747 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) ≠ (k X1 X0) ∨ (M.op (σ (τ X0)) (σ (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq64662 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq64662
    | (have j0 := eq64662 X0 X1
       grind)
    | exact resolve eq64662 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64662
  have eq64811 : ∀ X0 X1 : G, (M.op X0 (σ (τ X1))) = (M.op (σ (τ X1)) X0) ∨ X0 = X1 ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq64747 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq64747
    | (have j0 := eq64747 X0 X1
       grind)
    | exact resolve eq64747 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64747
  have eq64863 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq64811 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq64811
    | (have j0 := eq64811 X0 X1
       grind)
    | exact resolve eq64811 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64811
  have eq180873 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16287
       grind)
    | exact superpose eq16287 eq16
    | exact resolve eq16 eq16287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16287
  have eq180874 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq180873
       have r₂ := eq82 x
       grind)
    | exact resolve eq180873 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180873
  have eq180876 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq180874
       grind)
    | exact superpose eq180874 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq180874
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq180874
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq180874
       grind)
    | exact resolve eq12 eq180874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180874
  have eq180928 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq180876
  have eq180930 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq608
       have i₂ := eq180928
       grind)
    | exact superpose eq180928 eq608
    | exact resolve eq608 eq180928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq180928
  have eq180938 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq180930
  have eq180939 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq180938
  have eq180956 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq180939
       grind)
    | exact superpose eq180939 eq12
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq180939
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq180939
       grind)
    | exact resolve eq12 eq180939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180957 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq180939
       grind)
    | exact superpose eq180939 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq180939
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq180939
       grind)
    | exact resolve eq12 eq180939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180939
  have eq181009 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq180957
  have eq181010 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq180956
  have eq181016 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq181009
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq181009
    | exact resolve eq181009 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181009
  have eq181017 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq181010
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq181010
    | exact resolve eq181010 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181010
  have eq181021 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq181016
       grind)
    | exact superpose eq181016 eq16
    | exact resolve eq16 eq181016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181140 : (σ (k x y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq181016
       have i₂ := eq181017
       grind)
    | exact superpose eq181017 eq181016
    | exact resolve eq181016 eq181017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181016 eq181017
  have eq181229 : (σ x) = (σ y) ∨ (σ (k x y)) = (σ (k y x)) := by grind
  clear eq181140
  have eq181254 : y = (τ (σ x)) ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq181229
       grind)
    | exact superpose eq181229 eq10
    | exact resolve eq10 eq181229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181229
  have eq181559 : x = y ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq181254
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq181254
    | exact resolve eq181254 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181254
  have eq181561 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k x y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq181559
       grind)
    | exact superpose eq181559 eq16
    | exact resolve eq16 eq181559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181559
  have eq181562 : (σ (k x y)) = (σ (k y x)) := by
    first
    | (have r₁ := eq181561
       have r₂ := eq82 x
       grind)
    | exact resolve eq181561 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181561
  have eq181576 : (k y x) = (τ (σ (k x y))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq181562
       grind)
    | exact superpose eq181562 eq10
    | exact resolve eq10 eq181562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181562
  have eq181883 : (k x y) = (k y x) := by
    first
    | (have i₁ := eq181576
       have i₂ := eq10 (k x y)
       grind)
    | exact superpose eq10 eq181576
    | exact resolve eq181576 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181576
  have eq181915 : (k x y) ≠ (k x y) ∨ x = y ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq64863 x y
       have i₂ := eq181883
       grind)
    | exact superpose eq181883 eq64863
    | (have j0 := eq64863 x y
       grind)
    | (have r₁ := eq64863 x y
       have r₂ := eq181883
       grind)
    | (have r₁ := eq64863 y x
       have r₂ := eq181883
       grind)
    | exact resolve eq64863 eq181883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64863 eq181883
  have eq181930 : x = y ∨ (M.op x y) = (M.op y x) := by grind
  clear eq181915
  have eq182492 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq181930
       grind)
    | exact superpose eq181930 eq16
    | exact resolve eq16 eq181930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181930
  have eq182493 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq182492
       have r₂ := eq82 x
       grind)
    | exact resolve eq182492 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182492
  have eq182495 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq182493
       grind)
    | exact superpose eq182493 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq182493
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq182493
       grind)
    | exact resolve eq12 eq182493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182493
  have eq182547 : (M.op x y) = (k x y) := by grind
  clear eq182495
  have eq182552 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq181021
       have i₂ := eq182547
       grind)
    | exact superpose eq182547 eq181021
    | exact resolve eq181021 eq182547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181021 eq182547
  have eq182561 : (σ x) = (σ y) := by grind
  clear eq182552
  have eq182562 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq182561
       grind)
    | exact superpose eq182561 eq16
    | exact resolve eq16 eq182561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182563 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq182561
       grind)
    | exact superpose eq182561 eq10
    | exact resolve eq10 eq182561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182561
  have eq182868 : x = y := by
    first
    | (have i₁ := eq182563
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq182563
    | exact resolve eq182563 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182563
  have eq182869 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq182562
       have i₂ := eq82 x
       grind)
    | exact superpose eq82 eq182562
    | exact resolve eq182562 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq182562
  have eq182870 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq182869
       have i₂ := eq182868
       grind)
    | exact superpose eq182868 eq182869
    | exact resolve eq182869 eq182868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182868 eq182869
  have eq182871 : False := by grind
  exact eq182871
