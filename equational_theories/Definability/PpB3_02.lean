import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyx_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq13 X0 (M.op X0 X0)
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
  have eq177 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq16 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq16 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq16 X0 x x X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, x = (M.op (M.op (M.op X0 X1) x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x X0 X1 y
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (k X2 (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq16 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X0 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (k X2 (k (M.op X0 X1) (M.op X0 X1))) = (M.op (k (M.op X0 X1) (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq13 eq182
    | (have j0 := eq182 X0 X1 X2
       have j1 := eq13 X0 (M.op X0 X1)
       grind)
    | exact resolve eq182 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq184 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq177 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 x y X0
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y) X0
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq177 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq177
    | (have j0 := eq177 X0 x y
       grind)
    | exact resolve eq177 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 X0 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq177 X2 X0 x
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq177 X0 X0 X0
       grind)
    | exact superpose eq177 eq13
    | (have j0 := eq13 X0 X0
       grind)
    | exact resolve eq13 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (k X0 X0)) = (M.op (k X0 X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq13 eq195
    | (have j0 := eq195 X0 X1
       have j1 := eq13 X0 X0
       grind)
    | exact resolve eq195 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq197 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq184 eq177
    | exact resolve eq177 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X1 : G, (M.op x y) = (M.op x (M.op (M.op x y) X1)) := by
    intro X1
    first
    | exact superpose eq188 eq177
    | exact resolve eq177 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq764 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq28 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq28 X1 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq28 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq13 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq767 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (k X0 X1)) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X2 X1 X0
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq177
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq177 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq768 : ∀ X0 X1 X2 : G, (M.op (k X0 X1) (M.op X0 X2)) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X1 X0 X2
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq177
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq177 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq769 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 (M.op (k X0 X1) X2)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq178 X1 X0 x
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq178
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq178 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq777 : ∀ X0 : G, x = (M.op (k x X0) (M.op x y)) ∨ (M.op x x) = X0 := by
    intro X0
    first
    | (have i₁ := eq188 X0
       have i₂ := eq28 x X0
       grind)
    | exact superpose eq28 eq188
    | (have j1 := eq28 x X0
       grind)
    | exact resolve eq188 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq779 : ∀ X0 : G, (σ x) = (M.op (k (σ x) X0) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq189 x
       have i₂ := eq28 sF2 x
       grind)
    | exact superpose eq28 eq189
    | (have j1 := eq28 (σ x) X0
       grind)
    | exact resolve eq189 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq789 : ∀ X0 : G, x = (k (M.op x y) (M.op X0 x)) ∨ (M.op X0 x) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq188 X0
       have i₂ := eq28 sF0 (M.op X0 x)
       grind)
    | exact superpose eq28 eq188
    | (have j1 := eq28 (M.op x y) (M.op X0 x)
       grind)
    | exact resolve eq188 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq790 : ∀ X0 X1 : G, x = (k (M.op x y) (M.op (M.op X0 X1) x)) ∨ (M.op (M.op X0 X1) x) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq179 X0 X1
       have i₂ := eq28 sF0 (M.op (M.op X0 X1) x)
       grind)
    | exact superpose eq28 eq179
    | (have j1 := eq28 (M.op x y) (M.op (M.op X0 X1) x)
       grind)
    | exact resolve eq179 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq798 : (M.op x y) = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq803 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq805 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (k X0 (σ y))) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq185 X0
       have i₂ := eq28 X0 sF3
       grind)
    | exact superpose eq28 eq185
    | (have j1 := eq28 X0 (σ y)
       grind)
    | exact resolve eq185 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq808 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq28 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq809 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq764 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq764 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq764 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq811 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq798
       grind)
    | exact superpose eq798 eq40
    | exact resolve eq40 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq812 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq811
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq811
    | exact resolve eq811 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811
  have eq814 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq812
    | exact resolve eq812 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq816 : ∀ X0 X1 : G, (k X0 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq28 X0 X0
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq28 X1 X1
       grind)
    | (have r₁ := eq12 X0 (k X0 X0)
       have r₂ := eq28 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq28 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq819 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq820 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq819 X0
       have i₂ := eq177 X0 X0 X0
       grind)
    | (have i₁ := eq819 X0
       have i₂ := eq177 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq177 eq819
    | (have j0 := eq819 X0
       grind)
    | exact resolve eq819 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq819
  have eq821 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq820 X0
       have i₂ := eq177 X0 X0 X0
       grind)
    | (have i₁ := eq820 X0
       have i₂ := eq177 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq177 eq820
    | (have j0 := eq820 X0
       grind)
    | exact resolve eq820 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820
  have eq822 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq821
    | (have j0 := eq821 X0
       have j1 := eq28 X0 X0
       grind)
    | exact resolve eq821 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq828 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq808 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq808
    | (have j0 := eq808 (σ X0)
       grind)
    | exact resolve eq808 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq831 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq814 eq803
    | exact resolve eq803 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq838 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq831
       have r₂ := eq27
       grind)
    | exact resolve eq831 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq842 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq838
       have i₂ := eq28 sF3 sF3
       grind)
    | exact superpose eq28 eq838
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq838 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq845 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq838 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | exact resolve eq13 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq848 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq838 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq849 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ x)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq838 eq177
    | exact resolve eq177 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq854 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq838 eq191
    | exact resolve eq191 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq857 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq848 eq842
    | exact resolve eq842 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq842
  have eq891 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq838 eq849
    | exact resolve eq849 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq907 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq891
  have eq909 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq907
       have i₂ := eq28 sF2 sF2
       grind)
    | exact superpose eq28 eq907
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq907 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq915 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq907 eq28
    | (have j0 := eq28 y x
       grind)
    | exact resolve eq28 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq975 : ∀ X0 : G, (σ x) = (k (σ y) (M.op X0 (σ x))) ∨ (M.op X0 (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq854 eq28
    | (have j0 := eq28 (σ y) (M.op X0 (σ x))
       grind)
    | exact resolve eq28 eq854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq988 : ∀ X0 : G, (σ x) = (k (σ y) (M.op X0 (σ x))) ∨ (σ x) = (M.op X0 (σ x)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq838 eq975
    | (have j0 := eq975 X0
       grind)
    | exact resolve eq975 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq975
  have eq1007 : (τ (σ y)) = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq915 eq98
    | exact resolve eq98 eq915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq1013 : y = (k x x) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq32 eq1007
    | exact resolve eq1007 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1023 : (τ (σ x)) = (k y y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq857 eq116
    | exact resolve eq116 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq857
  have eq1030 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq1023
    | exact resolve eq1023 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq1115 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y y) ∨ x = (k y y) := by
    intro X0
    first
    | exact superpose eq1030 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1030
       grind)
    | exact resolve eq13 eq1030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1126 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y y) ∨ x = (k y y) := by
    intro X0
    first
    | (have j0 := eq1115 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1186 : (τ (σ y)) = (k x x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq909 eq98
    | exact resolve eq98 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq1195 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (k x x) := by
    first
    | exact superpose eq32 eq1186
    | exact resolve eq1186 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq1198 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq809 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq809
    | (have j0 := eq809 (σ X0) X1
       grind)
    | exact resolve eq809 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1213 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq909 eq822
    | (have j0 := eq822 (σ x)
       grind)
    | exact resolve eq822 eq909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq909
  have eq1217 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq848 eq822
    | (have j0 := eq822 (σ y)
       grind)
    | exact resolve eq822 eq848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq1221 : (σ y) = (k (σ y) (σ (k y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq37 (k y y)
       have i₂ := eq822 y
       grind)
    | exact superpose eq822 eq37
    | (have j1 := eq822 y
       grind)
    | exact resolve eq37 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq1228 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq1213
  have eq1234 : (σ y) = (k (σ y) (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1221
       have i₂ := eq41 y
       grind)
    | exact superpose eq41 eq1221
    | exact resolve eq1221 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1221
  have eq1238 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq814 eq1217
    | exact resolve eq1217 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1217
  have eq1250 : (σ y) = (k (σ y) (k (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1234
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1234
    | exact resolve eq1234 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1234
  have eq1254 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq838 eq1238
    | exact resolve eq1238 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238
  have eq1255 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq1254
  have eq1259 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq184 y
       have i₂ := eq1255
       grind)
    | exact superpose eq1255 eq184
    | exact resolve eq184 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1276 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1259 eq188
    | exact resolve eq188 eq1259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1259
  have eq1513 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y y) ∨ y = (k x x) := by
    intro X0
    first
    | exact superpose eq1195 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1195
       grind)
    | exact resolve eq13 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195
  have eq1524 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y y) ∨ y = (k x x) := by
    intro X0
    first
    | (have j0 := eq1513 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513
  have eq1559 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1228 eq153
    | exact resolve eq153 eq1228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq1228
  have eq1560 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq1559
    | exact resolve eq1559 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1559
  have eq1589 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1560 eq907
    | exact resolve eq907 eq1560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq907
  have eq1594 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (k x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1560 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1560
       grind)
    | exact resolve eq13 eq1560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1560
  have eq1605 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (k x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq1594 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594
  have eq1608 : x = (k x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq1589
  have eq1616 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq1608
       grind)
    | exact superpose eq1608 eq41
    | exact resolve eq41 eq1608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1608
  have eq1617 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1616
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1616
    | exact resolve eq1616 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616
  have eq1988 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq816 X0 (k X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816
  have eq1990 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq822 eq1988
    | (have j0 := eq1988 X0
       have j1 := eq822 (k X0 X0)
       grind)
    | exact resolve eq1988 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1988
  have eq2968 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (k y y) := by
    first
    | exact superpose eq1126 eq26
    | (have j1 := eq1126 (σ y)
       grind)
    | exact resolve eq26 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126
  have eq3044 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (k y y) := by
    first
    | exact superpose eq814 eq2968
    | exact resolve eq2968 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2968
  have eq3069 : x = (k y y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq3044
       have r₂ := eq27
       grind)
    | exact resolve eq3044 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3044
  have eq3083 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq3069
       grind)
    | exact superpose eq3069 eq41
    | exact resolve eq41 eq3069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3085 : y = (k y x) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq822 y
       have i₂ := eq3069
       grind)
    | exact superpose eq3069 eq822
    | (have j0 := eq822 y
       grind)
    | exact resolve eq822 eq3069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3088 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq798 eq3085
    | exact resolve eq3085 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798 eq3085
  have eq3089 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3083
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3083
    | exact resolve eq3083 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3083
  have eq3091 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3089
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3089
    | exact resolve eq3089 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3089
  have eq3115 : y = (k y y) ∨ y = (M.op x y) ∨ x = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3088
       have i₂ := eq28 y y
       grind)
    | exact superpose eq28 eq3088
    | (have j1 := eq28 y y
       grind)
    | exact resolve eq3088 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3122 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq3088
       grind)
    | exact superpose eq3088 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq3088
       grind)
    | exact resolve eq13 eq3088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3088
  have eq3139 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq3122 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3122
  have eq3143 : y = (M.op x y) ∨ x = (k y y) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq808 y
       grind)
    | (have r₁ := eq3115
       have r₂ := eq808 y
       grind)
    | exact resolve eq3115 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3115
  have eq3145 : x = (k y y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3069 eq3143
    | exact resolve eq3143 eq3069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3143
  have eq3148 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq3145
       grind)
    | exact superpose eq3145 eq41
    | exact resolve eq41 eq3145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3145
  have eq3154 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3148
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3148
    | exact resolve eq3148 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3148
  have eq3156 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq3154
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3154
    | exact resolve eq3154 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3154
  have eq3265 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq3091 eq1250
    | exact resolve eq1250 eq3091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3091
  have eq3266 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3156 eq1250
    | exact resolve eq1250 eq3156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3156
  have eq3271 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq814 eq3265
    | exact resolve eq3265 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3265
  have eq3355 : y = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (k y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3271
       have i₂ := eq28 y y
       grind)
    | exact superpose eq28 eq3271
    | (have j1 := eq28 y y
       grind)
    | exact resolve eq3271 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3363 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq3271
       grind)
    | exact superpose eq3271 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq3271
       grind)
    | exact resolve eq13 eq3271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3271
  have eq3380 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq3363 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3363
  have eq3388 : (σ (M.op x y)) = (σ y) ∨ x = (k y y) ∨ y = (M.op y y) := by
    first
    | (have j1 := eq808 y
       grind)
    | (have r₁ := eq3355
       have r₂ := eq808 y
       grind)
    | exact resolve eq3355 eq808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3355
  have eq3390 : x = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3069 eq3388
    | exact resolve eq3388 eq3069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3388
  have eq3393 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq3390
       grind)
    | exact superpose eq3390 eq41
    | exact resolve eq41 eq3390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3390
  have eq3399 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3393
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3393
    | exact resolve eq3393 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3393
  have eq3401 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3399
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3399
    | exact resolve eq3399 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3399
  have eq3404 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3401 eq1250
    | exact resolve eq1250 eq3401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1250 eq3401
  have eq4169 : x ≠ (k y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq3139
  have eq4185 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4169
       have r₂ := eq3069
       grind)
    | exact resolve eq4169 eq3069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4169
  have eq4207 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq184 y
       have i₂ := eq4185
       grind)
    | exact superpose eq4185 eq184
    | exact resolve eq184 eq4185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4215 : ∀ X0 : G, y = (M.op (M.op X0 y) x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq177 X0 y y
       have i₂ := eq4185
       grind)
    | exact superpose eq4185 eq177
    | exact resolve eq177 eq4185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4216 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq177 y y X0
       have i₂ := eq4185
       grind)
    | exact superpose eq4185 eq177
    | exact resolve eq177 eq4185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4239 : x = (M.op y (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4207 eq188
    | exact resolve eq188 eq4207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4242 : (M.op x y) = (M.op x x) ∨ y = (k x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4207 eq28
    | (have j0 := eq28 x (M.op x y)
       grind)
    | exact resolve eq28 eq4207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4268 : y = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4239 eq28
    | (have j0 := eq28 (M.op x y) y
       grind)
    | exact resolve eq28 eq4239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4371 : y = (M.op x x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4215 y
       have i₂ := eq4185
       grind)
    | exact superpose eq4185 eq4215
    | exact resolve eq4215 eq4185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4407 : y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq4371
  have eq4425 : y = (k x x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq4407
       grind)
    | exact superpose eq4407 eq28
    | exact resolve eq28 eq4407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4587 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq4425
       grind)
    | exact superpose eq4425 eq40
    | exact resolve eq40 eq4425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4425
  have eq4593 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4587
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4587
    | exact resolve eq4587 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4587
  have eq4595 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4593
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4593
    | exact resolve eq4593 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4593
  have eq4608 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq4595 eq822
    | (have j0 := eq822 (σ x)
       grind)
    | exact resolve eq822 eq4595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4610 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq4595 eq808
    | (have j0 := eq808 (σ x)
       grind)
    | exact resolve eq808 eq4595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4595
  have eq4774 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (k x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4407
       have i₂ := eq4242
       grind)
    | exact superpose eq4242 eq4407
    | exact resolve eq4407 eq4242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4242
  have eq4810 : y = (k x (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq4774
  have eq4816 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4810 eq42
    | exact resolve eq42 eq4810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4810
  have eq4818 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4816
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4816
    | exact resolve eq4816 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4816
  have eq4820 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4818
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4818
    | exact resolve eq4818 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4818
  have eq4933 : (M.op x y) = (M.op y y) ∨ x = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4268 eq197
    | exact resolve eq197 eq4268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4938 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4268 eq28
    | exact resolve eq28 eq4268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4956 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (k (M.op x y) y) := by grind
  clear eq4938
  have eq5023 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4185
       have i₂ := eq4933
       grind)
    | exact superpose eq4933 eq4185
    | exact resolve eq4185 eq4933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4933
  have eq5062 : x = (k (M.op x y) y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5023
  have eq7070 : x ≠ (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq3380
  have eq7116 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq7070
       have r₂ := eq3069
       grind)
    | exact resolve eq7070 eq3069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7070
  have eq7156 : y = (M.op (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq184 y
       have i₂ := eq7116
       grind)
    | exact superpose eq7116 eq184
    | exact resolve eq184 eq7116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7170 : ∀ X0 : G, y = (M.op (M.op X0 y) x) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq177 X0 y y
       have i₂ := eq7116
       grind)
    | exact superpose eq7116 eq177
    | exact resolve eq177 eq7116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7203 : x = (M.op y (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq7156 eq188
    | exact resolve eq188 eq7156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7294 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq7170 y
       have i₂ := eq7116
       grind)
    | exact superpose eq7116 eq7170
    | exact resolve eq7170 eq7116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7170
  have eq7338 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq7294
  have eq7372 : y = (k x x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq7338
       grind)
    | exact superpose eq7338 eq28
    | exact resolve eq28 eq7338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7635 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq7372
       grind)
    | exact superpose eq7372 eq40
    | exact resolve eq40 eq7372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7372
  have eq7645 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq7635
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7635
    | exact resolve eq7635 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7635
  have eq7647 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq7645
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7645
    | exact resolve eq7645 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7645
  have eq7662 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq7647 eq822
    | (have j0 := eq822 (σ x)
       grind)
    | exact resolve eq822 eq7647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7664 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq7647 eq808
    | (have j0 := eq808 (σ x)
       grind)
    | exact resolve eq808 eq7647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7647
  have eq11774 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq3266 eq803
    | exact resolve eq803 eq3266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3266
  have eq11785 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq838 eq11774
    | exact resolve eq11774 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11774
  have eq11786 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq11785
  have eq11801 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11786 eq177
    | exact resolve eq177 eq11786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11983 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq3404 eq803
    | exact resolve eq803 eq3404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3404
  have eq11999 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | exact superpose eq838 eq11983
    | exact resolve eq11983 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11983
  have eq12000 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq11999
  have eq12015 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq12000 eq177
    | exact resolve eq177 eq12000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12559 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq11786 eq11801
    | exact resolve eq11801 eq11786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11786 eq11801
  have eq12592 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq12559
  have eq12972 : ∀ X0 : G, y = (M.op (M.op X0 y) x) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq767 y y X0
       have i₂ := eq3069
       grind)
    | exact superpose eq3069 eq767
    | (have j0 := eq767 y y x
       grind)
    | exact resolve eq767 eq3069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12994 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4820 eq767
    | (have j0 := eq767 (σ x) (σ (M.op x y)) x
       grind)
    | exact resolve eq767 eq4820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13098 : ∀ X0 : G, y = (M.op (M.op X0 y) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq4215 eq12972
    | (have j0 := eq12972 X0
       have j1 := eq4215 X0
       grind)
    | exact resolve eq12972 eq4215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12972
  have eq13122 : ∀ X0 : G, y = (M.op (M.op X0 y) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq4215 eq13098
    | (have j0 := eq13098 X0
       have j1 := eq4215 X0
       grind)
    | exact resolve eq13098 eq4215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4215 eq13098
  have eq13131 : ∀ X0 : G, y = (M.op (M.op X0 y) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq28 eq13122
    | (have j0 := eq13122 X0
       have j1 := eq28 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq13122 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13122
  have eq13193 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq768 y y X0
       have i₂ := eq3069
       grind)
    | exact superpose eq3069 eq768
    | (have j0 := eq768 y y x
       grind)
    | exact resolve eq768 eq3069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3069
  have eq13215 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4820 eq768
    | (have j0 := eq768 (σ x) (σ (M.op x y)) x
       grind)
    | exact resolve eq768 eq4820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4820
  have eq13552 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq4216 eq13193
    | (have j0 := eq13193 X0
       have j1 := eq4216 X0
       grind)
    | exact resolve eq13193 eq4216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13193
  have eq13577 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq4216 eq13552
    | (have j0 := eq13552 X0
       have j1 := eq4216 X0
       grind)
    | exact resolve eq13552 eq4216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4216 eq13552
  have eq13584 : ∀ X0 : G, y = (M.op x (M.op y X0)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq28 eq13577
    | (have j0 := eq13577 X0
       have j1 := eq28 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq13577 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13577
  have eq13626 : ∀ X1 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X1)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f13626_14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = X1 := by
      intro X0 X1 X2
      grind
    have f13626_15 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
      intro X0
      grind
    have f13626_24 : (σ y) ≠ (M.op (σ (M.op x y)) (M.op (σ y) X1)) := by grind
    have f13626_25 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by grind
    have f13626_26 : y ≠ (M.op x y) := by grind
    have f13626_29 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) ∨ y = (M.op x y) := by
      intro X0
      first
      | (have j0 := f13626_15 X0
         grind)
      | (have r₁ := f13626_15 X0
         have r₂ := f13626_25
         grind)
      | exact resolve f13626_15 f13626_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f13626_30 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ y)) := by
      intro X0
      first
      | (have j0 := f13626_29 X0
         grind)
      | (have r₁ := f13626_29 X0
         have r₂ := f13626_26
         grind)
      | exact resolve f13626_29 f13626_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f13626_100 : ∀ X1 : G, (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) X1)) := by
      intro X1
      first
      | (have i₁ := f13626_14 (M.op x (σ (M.op x y))) (σ y) X1
         have i₂ := f13626_30 x
         grind)
      | exact superpose f13626_30 f13626_14
      | exact resolve f13626_14 f13626_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f13626_178 : (σ y) ≠ (σ y) := by
      first
      | (have i₁ := f13626_24
         have i₂ := f13626_100 X1
         grind)
      | exact superpose f13626_100 f13626_24
      | (have r₁ := f13626_24
         have r₂ := f13626_100 X1
         grind)
      | exact resolve f13626_24 f13626_100
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f13626_185 : False := by grind
    exact f13626_185
  have eq13666 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq13215
    | (have j0 := eq13215 (σ y)
       grind)
    | exact resolve eq13215 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13681 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq13215 eq177
    | exact resolve eq177 eq13215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13215
  have eq13776 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13666 eq13626
    | exact resolve eq13626 eq13666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13626 eq13666
  have eq13808 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq13776
  have eq14452 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq12000 eq12015
    | exact resolve eq12015 eq12000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12000 eq12015
  have eq14495 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq14452
  have eq17361 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (k x x) := by
    first
    | exact superpose eq1524 eq26
    | (have j1 := eq1524 (σ y)
       grind)
    | exact resolve eq26 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1524
  have eq17512 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (k x x) := by
    first
    | exact superpose eq814 eq17361
    | exact resolve eq17361 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17361
  have eq17549 : x = (M.op y y) ∨ y = (k x x) := by
    first
    | (have r₁ := eq17512
       have r₂ := eq27
       grind)
    | exact resolve eq17512 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17512
  have eq17574 : (M.op x y) = (k x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq4185 eq17549
    | exact resolve eq17549 eq4185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17549
  have eq17627 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq17574
       grind)
    | exact superpose eq17574 eq40
    | exact resolve eq40 eq17574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17629 : x = (k x (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq822 x
       have i₂ := eq17574
       grind)
    | exact superpose eq17574 eq822
    | (have j0 := eq822 x
       grind)
    | exact resolve eq822 eq17574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17631 : x ≠ (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq808 x
       have i₂ := eq17574
       grind)
    | exact superpose eq17574 eq808
    | (have j0 := eq808 x
       grind)
    | exact resolve eq808 eq17574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17632 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x X0)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq768 x x X0
       have i₂ := eq17574
       grind)
    | exact superpose eq17574 eq768
    | (have j0 := eq768 x x x
       grind)
    | exact resolve eq768 eq17574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17644 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17627
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17627
    | exact resolve eq17627 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17627
  have eq17646 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq17644
    | exact resolve eq17644 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17644
  have eq17648 : (σ y) = (k (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq7116 eq17646
    | exact resolve eq17646 eq7116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17646
  have eq17912 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq13131 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13131
    | (have j0 := eq13131 x
       grind)
    | exact resolve eq13131 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17946 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq188 (M.op x y)
       have i₂ := eq13131 x
       grind)
    | exact superpose eq13131 eq188
    | exact resolve eq188 eq13131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17961 : ∀ X1 : G, x = (M.op y (M.op x X1)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X1
    first
    | (have i₁ := eq177 (M.op x y) x X1
       have i₂ := eq13131 x
       grind)
    | exact superpose eq13131 eq177
    | exact resolve eq177 eq13131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13131
  have eq18000 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq17912 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq17912
       grind)
    | exact resolve eq13 eq17912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18023 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq18000 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18000
  have eq18303 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op y (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq17946 eq207
    | exact resolve eq207 eq17946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18308 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (M.op y (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq17946 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq17946
       grind)
    | exact resolve eq13 eq17946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18331 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (M.op y (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq18308 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18308
  have eq18923 : x = (M.op (k x (σ x)) (M.op x y)) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1605 eq188
    | exact resolve eq188 eq1605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18947 : (M.op x y) = (M.op (k (M.op x y) (σ x)) y) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1605 eq197
    | exact resolve eq197 eq1605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1605
  have eq19039 : (M.op x y) = (M.op (k (M.op x y) (σ x)) (M.op x y)) ∨ x = (k x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq4185 eq18947
    | exact resolve eq18947 eq4185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18947
  have eq19041 : x = (M.op (k x (σ x)) (M.op x y)) ∨ x = (k x (M.op x y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq4185 eq18923
    | exact resolve eq18923 eq4185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18923
  have eq19090 : (M.op x y) = (M.op (k (M.op x y) (σ x)) (M.op x y)) ∨ x = (k x (M.op x y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq4185 eq19039
    | exact resolve eq19039 eq4185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19039
  have eq19829 : y = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq13584 (M.op x x)
       have i₂ := eq17961 x
       grind)
    | exact superpose eq17961 eq13584
    | exact resolve eq13584 eq17961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13584 eq17961
  have eq19853 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq19829
  have eq19873 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq19853 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq19853
       grind)
    | exact resolve eq13 eq19853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19896 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq19873 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19873
  have eq20758 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17632 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17632
    | (have j0 := eq17632 y
       grind)
    | exact resolve eq17632 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17632
  have eq22121 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq18023 eq17912
    | exact resolve eq17912 eq18023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18023
  have eq22212 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq22121
  have eq22262 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq22212 eq828
    | (have j0 := eq828 (M.op x y)
       grind)
    | exact resolve eq828 eq22212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22270 : x ≠ (M.op x y) ∨ y = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq22212
  have eq22273 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq22262
  have eq22276 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq22273
    | exact resolve eq22273 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22273
  have eq22279 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7156 eq22276
    | exact resolve eq22276 eq7156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7156 eq22276
  have eq22301 : (σ x) = (σ y) ∨ y = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq838 eq22279
    | exact resolve eq22279 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22279
  have eq22362 : (σ x) = (σ y) ∨ y = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4207 eq22301
    | exact resolve eq22301 eq4207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22301
  have eq22367 : (σ x) = (σ y) ∨ y = (M.op (M.op x y) x) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17912 eq22362
    | exact resolve eq22362 eq17912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17912 eq22362
  have eq22370 : y = (M.op (M.op x y) x) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq22367
       have r₂ := eq22270
       grind)
    | exact resolve eq22367 eq22270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22270 eq22367
  have eq22380 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq22370 eq188
    | exact resolve eq188 eq22370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22396 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq22370 eq177
    | exact resolve eq177 eq22370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22370
  have eq22425 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq22380 eq42
    | exact resolve eq42 eq22380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22435 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq20 eq22425
    | exact resolve eq22425 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22425
  have eq22438 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq22435
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22435
    | exact resolve eq22435 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22435
  have eq22441 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq1276 eq22438
    | exact resolve eq22438 eq1276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22438
  have eq23027 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op y (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op y (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq18331 eq17946
    | exact resolve eq17946 eq18331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23060 : x = (M.op (k x (M.op x y)) (M.op x y)) ∨ x = (M.op y (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq18331 eq188
    | exact resolve eq188 eq18331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18331
  have eq23119 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op y (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq23027
  have eq23179 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq23119 eq42
    | exact resolve eq42 eq23119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23188 : x ≠ (M.op x y) ∨ x = (M.op y (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq23119
  have eq23196 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq23179
    | exact resolve eq23179 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23179
  have eq23199 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op y (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7203 eq23196
    | exact resolve eq23196 eq7203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23196
  have eq23202 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq22380 eq23199
    | exact resolve eq23199 eq22380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22380 eq23199
  have eq23941 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op y (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq23202 eq142
    | exact resolve eq142 eq23202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23202
  have eq23966 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op y (M.op x y)) ∨ x = (k x x) := by
    first
    | exact superpose eq30 eq23941
    | exact resolve eq23941 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23941
  have eq24175 : ∀ X0 : G, x ≠ (M.op x x) ∨ (k X0 (k x x)) = (M.op (k x x) X0) ∨ x = (k x (M.op x y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq19041 eq183
    | exact resolve eq183 eq19041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183 eq19041
  have eq24192 : ∀ X0 : G, (k X0 (k x x)) = (M.op (k x x) X0) ∨ x = (k x (M.op x y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq24175 X0
       grind)
    | (have r₁ := eq24175 X0
       have r₂ := eq17629
       grind)
    | exact resolve eq24175 eq17629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17629 eq24175
  have eq24193 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (k x (M.op x y)) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq17574 eq24192
    | exact resolve eq24192 eq17574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24192
  have eq24322 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (k x (M.op x y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq19090 eq197
    | exact resolve eq197 eq19090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19090
  have eq24352 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq4185 eq24322
    | exact resolve eq24322 eq4185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24322
  have eq26404 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq19896 eq19853
    | exact resolve eq19853 eq19896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19896
  have eq26503 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq26404
  have eq26582 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26503 eq828
    | (have j0 := eq828 (M.op x y)
       grind)
    | exact resolve eq828 eq26503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26590 : x ≠ (M.op x y) ∨ y = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq26503
  have eq26593 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by grind
  clear eq26582
  have eq26597 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq26593
    | exact resolve eq26593 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26593
  have eq26600 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq7338 eq26597
    | exact resolve eq26597 eq7338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7338 eq26597
  have eq26603 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq838 eq26600
    | exact resolve eq26600 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26600
  have eq26668 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4407 eq26603
    | exact resolve eq26603 eq4407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4407 eq26603
  have eq26672 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19853 eq26668
    | exact resolve eq26668 eq19853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19853 eq26668
  have eq26674 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq26672
       have r₂ := eq26590
       grind)
    | exact resolve eq26672 eq26590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26590 eq26672
  have eq26703 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq22396 x
       have i₂ := eq26674
       grind)
    | exact superpose eq26674 eq22396
    | exact resolve eq22396 eq26674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22396 eq26674
  have eq26748 : x = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq26703
  have eq27005 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq26748 eq808
    | (have j0 := eq808 (M.op x y)
       grind)
    | exact resolve eq808 eq26748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808 eq26748
  have eq30759 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) ∨ x = (M.op y y) ∨ x = (k x (M.op x y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq24193 eq24352
    | exact resolve eq24352 eq24193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24193
  have eq30876 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (k x (M.op x y)) ∨ x = (M.op y y) := by grind
  clear eq30759
  have eq30948 : x = (M.op x y) ∨ x = (k x (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op y (M.op x y)) ∨ x = (k x x) := by
    first
    | exact superpose eq23966 eq30876
    | exact resolve eq30876 eq23966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23966 eq30876
  have eq31001 : x = (M.op x y) ∨ x = (k x (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (k x x) := by
    first
    | exact superpose eq4185 eq30948
    | exact resolve eq30948 eq4185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30948
  have eq31007 : x = (M.op x y) ∨ x = (k x (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ x = (k x x) := by
    first
    | exact superpose eq24352 eq31001
    | exact resolve eq31001 eq24352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24352 eq31001
  have eq31008 : x = (M.op x y) ∨ x = (k x (M.op x y)) ∨ x = (M.op y y) ∨ x = (k x x) := by grind
  clear eq31007
  have eq31014 : x = (M.op x y) ∨ x = (k x (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17574 eq31008
    | exact resolve eq31008 eq17574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17574 eq31008
  have eq31015 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq31014
  have eq31042 : x = (M.op x (M.op x y)) ∨ x = (M.op y (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq31015 eq23060
    | exact resolve eq23060 eq31015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23060 eq31015
  have eq31079 : x = (M.op x (M.op x y)) ∨ x = (M.op y (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq31042
       have r₂ := eq23188
       grind)
    | exact resolve eq31042 eq23188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31042
  have eq31089 : x = (M.op x (M.op x y)) ∨ x = (M.op y (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4239 eq31079
    | exact resolve eq31079 eq4239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31079
  have eq31098 : x = (M.op x (M.op x y)) ∨ x = (M.op y (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17946 eq31089
    | exact resolve eq31089 eq17946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17946 eq31089
  have eq31105 : x = (M.op x (M.op x y)) ∨ x = (M.op y (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq31098
       have r₂ := eq23188
       grind)
    | exact resolve eq31098 eq23188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31098
  have eq31108 : x = (M.op x y) ∨ x = (M.op y (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq18303 eq31105
    | exact resolve eq31105 eq18303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18303 eq31105
  have eq31110 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have r₁ := eq31108
       have r₂ := eq23188
       grind)
    | exact resolve eq31108 eq23188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23188 eq31108
  have eq31200 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq31110 eq42
    | exact resolve eq42 eq31110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31205 : (σ x) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq31110 eq828
    | (have j0 := eq828 (M.op x y)
       grind)
    | exact resolve eq828 eq31110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31206 : ∀ X0 : G, (σ x) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq31110 eq1198
    | (have j0 := eq1198 (M.op x y) X0
       grind)
    | exact resolve eq1198 eq31110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31213 : ∀ X0 : G, (σ x) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq31206
    | (have j0 := eq31206 X0
       grind)
    | exact resolve eq31206 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31206
  have eq31214 : (σ x) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq20 eq31205
    | exact resolve eq31205 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31205
  have eq31215 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq20 eq31200
    | exact resolve eq31200 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31200
  have eq31218 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq31213 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31213
    | (have j0 := eq31213 X0
       grind)
    | exact resolve eq31213 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31213
  have eq31219 : (σ (M.op x y)) ≠ (σ x) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq31214
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31214
    | exact resolve eq31214 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31214
  have eq31220 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq31215
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31215
    | exact resolve eq31215 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31215
  have eq31223 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq20 eq31218
    | (have j0 := eq31218 X0
       grind)
    | exact resolve eq31218 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31218
  have eq31224 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq20 eq31219
    | exact resolve eq31219 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31219
  have eq31225 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq7203 eq31220
    | exact resolve eq31220 eq7203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31220
  have eq31228 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq7203 eq31223
    | exact resolve eq31223 eq7203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31223
  have eq31229 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq7203 eq31224
    | exact resolve eq31224 eq7203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31224
  have eq31231 : ∀ X0 : G, (σ x) ≠ (σ y) ∨ (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq7203 eq31228
    | (have j0 := eq31228 X0
       grind)
    | exact resolve eq31228 eq7203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31228
  have eq31232 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq7203 eq31229
    | exact resolve eq31229 eq7203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7203 eq31229
  have eq32389 : x = (k (M.op x y) (M.op y x)) ∨ y = (M.op y x) ∨ x = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4268 eq790
    | exact resolve eq790 eq4268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4268
  have eq32397 : x = (k (M.op x y) (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20758 eq790
    | exact resolve eq790 eq20758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq32514 : x = (k (M.op x y) (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq32397
  have eq32517 : x = (k (M.op x y) (M.op x x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq789 eq32514
    | (have j1 := eq789 x
       grind)
    | exact resolve eq32514 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789 eq32514
  have eq32522 : (M.op x y) = (k (M.op x y) (M.op y (M.op x y))) ∨ y = (M.op y x) ∨ x = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5062 eq32389
    | exact resolve eq32389 eq5062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32389
  have eq32525 : x = (k (M.op x y) x) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20758 eq32517
    | exact resolve eq32517 eq20758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20758 eq32517
  have eq32528 : (M.op x y) = (k (M.op x y) (M.op y (M.op x y))) ∨ y = (M.op y (M.op x y)) ∨ x = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5062 eq32522
    | exact resolve eq32522 eq5062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32522
  have eq32533 : (M.op x y) = (k (M.op x y) x) ∨ y = (M.op y (M.op x y)) ∨ x = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4239 eq32528
    | exact resolve eq32528 eq4239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32528
  have eq32537 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op y (M.op x y)) ∨ x = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5062 eq32533
    | exact resolve eq32533 eq5062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32533
  have eq32541 : y = (M.op x y) ∨ y = (M.op y (M.op x y)) ∨ x = (k (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4956 eq32537
    | exact resolve eq32537 eq4956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4956 eq32537
  have eq32542 : y = (M.op x y) ∨ y = (M.op y (M.op x y)) ∨ x = (k (M.op x y) y) := by grind
  clear eq32541
  have eq32546 : y = (M.op x y) ∨ x = y ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq4239 eq32542
    | exact resolve eq32542 eq4239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32542
  have eq32550 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (k (M.op x y) y) := by
    first
    | exact superpose eq5062 eq32546
    | exact resolve eq32546 eq5062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5062 eq32546
  have eq32551 : x = (k (M.op x y) y) ∨ y = (M.op x y) := by grind
  clear eq32550
  have eq32927 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32551 eq41
    | exact resolve eq41 eq32551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32551
  have eq32943 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq32927
    | exact resolve eq32927 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32927
  have eq32945 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32943
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32943
    | exact resolve eq32943 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32943
  have eq32952 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) X0)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq32945 eq768
    | (have j0 := eq768 (σ (M.op x y)) (σ y) x
       grind)
    | exact resolve eq768 eq32945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32945
  have eq32959 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq32525 eq38
    | exact resolve eq38 eq32525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32525
  have eq32972 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq32959
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq32959
    | exact resolve eq32959 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32959
  have eq32974 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq7116 eq32972
    | exact resolve eq32972 eq7116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32972
  have eq32976 : (σ (M.op x y)) = (σ x) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq814 eq32974
    | exact resolve eq32974 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32974
  have eq32978 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq7116 eq32976
    | exact resolve eq32976 eq7116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7116 eq32976
  have eq33008 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq32978 eq207
    | exact resolve eq207 eq32978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34114 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq13808 eq32952
    | exact resolve eq32952 eq13808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13808 eq32952
  have eq34186 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by grind
  clear eq34114
  have eq34188 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq34186
    | exact resolve eq34186 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34186
  have eq34190 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq34188
       have r₂ := eq27
       grind)
    | exact resolve eq34188 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34188
  have eq34236 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq34190 eq12994
    | exact resolve eq12994 eq34190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12994 eq34190
  have eq34276 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq34236
  have eq42614 : y = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1990 x
       have i₂ := eq1013
       grind)
    | exact superpose eq1013 eq1990
    | (have j0 := eq1990 y
       grind)
    | exact resolve eq1990 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42777 : y = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by grind
  clear eq42614
  have eq42820 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq4185 eq42777
    | exact resolve eq42777 eq4185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4185 eq42777
  have eq42831 : x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq32978 eq42820
    | exact resolve eq42820 eq32978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32978 eq42820
  have eq42837 : x = (M.op y y) ∨ x = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq42831
       have r₂ := eq17631
       grind)
    | exact resolve eq42831 eq17631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17631 eq42831
  have eq42840 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq33008 eq42837
    | exact resolve eq42837 eq33008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33008 eq42837
  have eq43156 : y = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq184 y
       have i₂ := eq42840
       grind)
    | exact superpose eq42840 eq184
    | exact resolve eq184 eq42840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43186 : ∀ X0 : G, y = (M.op (M.op X0 y) x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq177 X0 y y
       have i₂ := eq42840
       grind)
    | exact superpose eq42840 eq177
    | exact resolve eq177 eq42840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43253 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq43156 eq188
    | exact resolve eq188 eq43156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43156
  have eq43421 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq43186 y
       have i₂ := eq42840
       grind)
    | exact superpose eq42840 eq43186
    | exact resolve eq43186 eq42840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42840 eq43186
  have eq43505 : y = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq43421
  have eq51851 : x = (M.op y (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq777 x
       have i₂ := eq1013
       grind)
    | exact superpose eq1013 eq777
    | (have j0 := eq777 x
       grind)
    | exact resolve eq777 eq1013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777 eq1013
  have eq51970 : x = (M.op y (M.op x y)) ∨ x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq4239 eq51851
    | exact resolve eq51851 eq4239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51851
  have eq51973 : x = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq43253 eq51970
    | exact resolve eq51970 eq43253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51970
  have eq51975 : x = (M.op y (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq43253 eq51973
    | exact resolve eq51973 eq43253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43253 eq51973
  have eq51976 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq51975
  have eq52032 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq51976 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq51976
       grind)
    | exact resolve eq13 eq51976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52073 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq52032 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52032
  have eq52918 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq52073 eq51976
    | exact resolve eq51976 eq52073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51976 eq52073
  have eq53060 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq52918
  have eq53188 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq53060 eq42
    | exact resolve eq42 eq53060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq53202 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq53060 eq828
    | (have j0 := eq828 (M.op x y)
       grind)
    | exact resolve eq828 eq53060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53203 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq53060 eq1198
    | (have j0 := eq1198 (M.op x y) X0
       grind)
    | exact resolve eq1198 eq53060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53060
  have eq53212 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq53203 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53203
  have eq53213 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq53202
  have eq53238 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq20 eq53212
    | (have j0 := eq53212 X0
       grind)
    | exact resolve eq53212 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53212
  have eq53239 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq53213
    | exact resolve eq53213 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53213
  have eq53240 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq53188
    | exact resolve eq53188 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53188
  have eq53245 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq1276 eq53238
    | exact resolve eq53238 eq1276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53238
  have eq53246 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1276 eq53239
    | exact resolve eq53239 eq1276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53239
  have eq53247 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1276 eq53240
    | exact resolve eq53240 eq1276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276 eq53240
  have eq53252 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq53245 X0
       have j1 := eq31231 X0
       grind)
    | (have r₁ := eq53245 X0
       have r₂ := eq31231 X0
       grind)
    | exact resolve eq53245 eq31231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31231 eq53245
  have eq53253 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have r₁ := eq53246
       have r₂ := eq31232
       grind)
    | exact resolve eq53246 eq31232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31232 eq53246
  have eq53254 : (σ x) = (σ y) ∨ x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22441 eq53247
    | exact resolve eq53247 eq22441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22441 eq53247
  have eq53255 : x = (M.op y (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq53254
  have eq53454 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq53253 eq185
    | exact resolve eq185 eq53253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53481 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (k (σ y) (σ y))) = (M.op (k (σ y) (σ y)) X0) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq53253 eq196
    | (have j0 := eq196 (σ y) X0
       grind)
    | (have r₁ := eq196 (σ y) x
       have r₂ := eq53253
       grind)
    | exact resolve eq196 eq53253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq53494 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ y)) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq53253 eq191
    | exact resolve eq191 eq53253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53253
  have eq53524 : ∀ X0 : G, (k X0 (k (σ y) (σ y))) = (M.op (k (σ y) (σ y)) X0) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq53481 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53481
  have eq53536 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq53255 eq53494
    | exact resolve eq53494 eq53255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53494
  have eq53542 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq31225 eq53524
    | exact resolve eq53524 eq31225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31225 eq53524
  have eq53548 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq53255 eq53454
    | exact resolve eq53454 eq53255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53454
  have eq54428 : (M.op x y) = (M.op (k (M.op x y) (σ y)) y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq53252 eq197
    | exact resolve eq197 eq53252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53252
  have eq54496 : (M.op x y) = (M.op (k (M.op x y) (σ y)) (M.op x y)) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq4239 eq54428
    | exact resolve eq54428 eq4239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54428
  have eq54546 : (M.op x y) = (M.op (k (M.op x y) (σ x)) (M.op x y)) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq53255 eq54496
    | exact resolve eq54496 eq53255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53255 eq54496
  have eq54698 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y (M.op x y)) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq53548 eq53536
    | exact resolve eq53536 eq53548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53536 eq53548
  have eq54760 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y (M.op x y)) := by grind
  clear eq54698
  have eq55393 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq4608 eq779
    | (have j0 := eq779 (σ y)
       grind)
    | exact resolve eq779 eq4608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4608
  have eq55395 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq7662 eq779
    | (have j0 := eq779 (σ y)
       grind)
    | exact resolve eq779 eq7662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7662
  have eq55458 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14495 eq55395
    | exact resolve eq55395 eq14495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55395
  have eq55459 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3, g4⟩ := hcon
    have f55459_16 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by grind
    have f55459_17 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
    have f55459_26 : (σ x) ≠ (M.op (σ x) (σ y)) := by grind
    have f55459_27 : (σ y) ≠ (M.op (σ x) (σ x)) := by grind
    have f55459_28 : (σ x) ≠ (M.op (σ x) (σ x)) := by grind
    have f55459_29 : x ≠ y := by grind
    have f55459_30 : y ≠ (M.op x y) := by grind
    have f55459_33 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
      first
      | (have r₁ := f55459_17
         have r₂ := f55459_27
         grind)
      | exact resolve f55459_17 f55459_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f55459_34 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
      first
      | (have r₁ := f55459_16
         have r₂ := f55459_27
         grind)
      | exact resolve f55459_16 f55459_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f55459_35 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
      first
      | (have r₁ := f55459_33
         have r₂ := f55459_29
         grind)
      | exact resolve f55459_33 f55459_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f55459_36 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y ∨ y = (M.op x y) := by
      first
      | (have r₁ := f55459_34
         have r₂ := f55459_28
         grind)
      | exact resolve f55459_34 f55459_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f55459_37 : (σ y) = (M.op (σ x) (σ y)) := by
      first
      | (have r₁ := f55459_35
         have r₂ := f55459_30
         grind)
      | exact resolve f55459_35 f55459_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f55459_38 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
      first
      | (have r₁ := f55459_36
         have r₂ := f55459_29
         grind)
      | exact resolve f55459_36 f55459_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f55459_39 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
      first
      | (have r₁ := f55459_38
         have r₂ := f55459_30
         grind)
      | exact resolve f55459_38 f55459_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f55459_40 : (σ x) = (M.op (σ x) (σ y)) := by
      first
      | (have i₁ := f55459_39
         have i₂ := f55459_37
         grind)
      | exact superpose f55459_37 f55459_39
      | exact resolve f55459_39 f55459_37
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f55459_41 : False := by
      first
      | (have r₁ := f55459_40
         have r₂ := f55459_26
         grind)
      | exact resolve f55459_40 f55459_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f55459_41
  clear eq55393
  have eq55464 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq55458
    | exact resolve eq55458 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55458
  have eq55465 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq55459
    | exact resolve eq55459 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55459
  have eq55467 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq14495 eq55464
    | exact resolve eq55464 eq14495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14495 eq55464
  have eq55468 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq12592 eq55465
    | exact resolve eq55465 eq12592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55465
  have eq55469 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq55467
       have r₂ := eq7664
       grind)
    | exact resolve eq55467 eq7664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7664 eq55467
  have eq55470 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq55468
       have r₂ := eq4610
       grind)
    | exact resolve eq55468 eq4610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4610 eq55468
  have eq55684 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y (M.op x y)) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq53542 eq54760
    | exact resolve eq54760 eq53542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53542 eq54760
  have eq55834 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y (M.op x y)) := by grind
  clear eq55684
  have eq55957 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq55834 eq142
    | exact resolve eq142 eq55834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq55834
  have eq55998 : x = (k x x) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq30 eq55957
    | exact resolve eq55957 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55957
  have eq56062 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1990 x
       have i₂ := eq55998
       grind)
    | exact superpose eq55998 eq1990
    | (have j0 := eq1990 x
       grind)
    | exact resolve eq1990 eq55998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1990 eq55998
  have eq56067 : x = (M.op y (M.op x y)) ∨ x = (M.op x x) := by grind
  clear eq56062
  have eq56111 : y = (M.op (M.op x y) x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq56067 eq184
    | exact resolve eq184 eq56067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56067
  have eq56234 : (M.op x y) = (M.op x x) ∨ y = (k x (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq56111 eq28
    | (have j0 := eq28 x (M.op x y)
       grind)
    | exact resolve eq28 eq56111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56111
  have eq56677 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq54546 eq197
    | exact resolve eq197 eq54546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54546
  have eq56732 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq4239 eq56677
    | exact resolve eq56677 eq4239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4239 eq56677
  have eq56792 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | exact superpose eq56732 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq56732
       grind)
    | exact resolve eq13 eq56732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56832 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (M.op y (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq56792 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56792
  have eq57904 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op y (M.op x y)) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq56832 eq56732
    | exact resolve eq56732 eq56832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56732 eq56832
  have eq58044 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op y (M.op x y)) := by grind
  clear eq57904
  have eq58124 : x = (M.op x y) ∨ x = (M.op y (M.op x y)) ∨ x = (M.op y (M.op x y)) := by
    first
    | exact superpose eq58044 eq31110
    | exact resolve eq31110 eq58044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31110 eq58044
  have eq58161 : x = (M.op y (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq58124
  have eq58198 : y = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58161 eq184
    | exact resolve eq184 eq58161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58230 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq58161 eq178
    | exact resolve eq178 eq58161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58161
  have eq58322 : (M.op x y) = (M.op x x) ∨ y = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq58198 eq28
    | (have j0 := eq28 x (M.op x y)
       grind)
    | exact resolve eq28 eq58198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65756 : y = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq188 x
       have i₂ := eq58322
       grind)
    | exact superpose eq58322 eq188
    | exact resolve eq188 eq58322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65776 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq58322
       grind)
    | exact superpose eq58322 eq28
    | exact resolve eq28 eq58322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65815 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ y = (k x (M.op x y)) := by grind
  clear eq65776
  have eq66660 : x = (k x (M.op x y)) ∨ x = (M.op x x) ∨ x = (M.op x y) ∨ y = (k x (M.op x y)) := by
    first
    | (have i₁ := eq822 x
       have i₂ := eq65815
       grind)
    | exact superpose eq65815 eq822
    | (have j0 := eq822 x
       grind)
    | exact resolve eq822 eq65815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65815
  have eq66684 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (k x (M.op x y)) := by
    first
    | exact superpose eq58322 eq66660
    | exact resolve eq66660 eq58322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58322 eq66660
  have eq66685 : y = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by grind
  clear eq66684
  have eq67042 : x ≠ y ∨ x = (M.op x y) ∨ x = (k x (M.op x y)) := by grind
  clear eq66685
  have eq92624 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (k x (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq188 x
       have i₂ := eq56234
       grind)
    | exact superpose eq56234 eq188
    | exact resolve eq188 eq56234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq56234
  have eq92710 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq65756 eq92624
    | exact resolve eq92624 eq65756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92624
  have eq98315 : x ≠ (M.op x y) ∨ y = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq92710
  have eq98335 : y = (k x (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq98315
       have r₂ := eq65756
       grind)
    | exact resolve eq98315 eq65756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65756 eq98315
  have eq98410 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq98335 eq768
    | (have j0 := eq768 x (M.op x y) x
       grind)
    | exact resolve eq768 eq98335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98335
  have eq98417 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq58230 eq98410
    | (have j0 := eq98410 X0
       have j1 := eq58230 X0
       grind)
    | exact resolve eq98410 eq58230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98410
  have eq98440 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq58230 eq98417
    | (have j0 := eq98417 X0
       have j1 := eq58230 X0
       grind)
    | exact resolve eq98417 eq58230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58230 eq98417
  have eq98441 : ∀ X0 : G, x = (M.op y (M.op x X0)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq98440 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98440
  have eq98526 : x = (M.op y y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq98441 x
       have i₂ := eq43505
       grind)
    | exact superpose eq43505 eq98441
    | exact resolve eq98441 eq43505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43505
  have eq98556 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq184 (M.op x x)
       have i₂ := eq98441 x
       grind)
    | exact superpose eq98441 eq184
    | exact resolve eq184 eq98441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq98441
  have eq98632 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq98526
       have r₂ := eq27005
       grind)
    | exact resolve eq98526 eq27005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27005 eq98526
  have eq98733 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (M.op (M.op x y) x) := by
    intro X0
    first
    | exact superpose eq98556 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq98556
       grind)
    | exact resolve eq13 eq98556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98784 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ y = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have j0 := eq98733 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98733
  have eq99691 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) x) ∨ y = (M.op (M.op x y) x) := by
    first
    | exact superpose eq98784 eq98556
    | exact resolve eq98556 eq98784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98556
  have eq99863 : y ≠ (k x (M.op x y)) ∨ y = (M.op (M.op x y) x) := by grind
  clear eq98784
  have eq99866 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) x) := by grind
  clear eq99691
  have eq99878 : (M.op x y) ≠ (k x (M.op x y)) ∨ y = (M.op (M.op x y) x) := by
    first
    | exact superpose eq4207 eq99863
    | exact resolve eq99863 eq4207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4207 eq99863
  have eq99916 : (M.op x y) ≠ (k (M.op x y) (M.op x y)) ∨ y = (M.op (M.op x y) x) := by
    first
    | exact superpose eq58198 eq99878
    | exact resolve eq99878 eq58198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58198 eq99878
  have eq99938 : y = (M.op (M.op x y) x) := by
    first
    | (have r₁ := eq99916
       have r₂ := eq99866
       grind)
    | exact resolve eq99916 eq99866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99866 eq99916
  have eq100025 : ∀ X0 : G, y = (M.op (M.op X0 y) x) := by
    intro X0
    first
    | exact superpose eq99938 eq191
    | exact resolve eq191 eq99938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq99938
  have eq103135 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq98632 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq98632
       grind)
    | exact resolve eq13 eq98632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103190 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq103135 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103135
  have eq114840 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq103190 eq98632
    | exact resolve eq98632 eq103190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98632 eq103190
  have eq115067 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq114840
  have eq115306 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq115067 eq828
    | (have j0 := eq828 (M.op x y)
       grind)
    | exact resolve eq828 eq115067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828
  have eq115307 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq115067 eq1198
    | (have j0 := eq1198 (M.op x y) X0
       grind)
    | exact resolve eq1198 eq115067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115067
  have eq115316 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq115307 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115307
  have eq115317 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq115306
  have eq115346 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq20 eq115316
    | (have j0 := eq115316 X0
       grind)
    | exact resolve eq115316 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115316
  have eq115347 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq115317
    | exact resolve eq115317 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115317
  have eq115354 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq1255 eq115346
    | exact resolve eq115346 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115346
  have eq115355 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1255 eq115347
    | exact resolve eq115347 eq1255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255 eq115347
  have eq115361 : ∀ X0 : G, (k X0 (σ y)) = (M.op (σ y) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq115354 X0
       have j1 := eq845 X0
       grind)
    | (have r₁ := eq115354 X0
       have r₂ := eq845 X0
       grind)
    | exact resolve eq115354 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845 eq115354
  have eq115362 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq838 eq115355
    | exact resolve eq115355 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq838 eq115355
  have eq115363 : x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq115362
  have eq116789 : (σ x) = (M.op (k (σ x) (σ y)) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq115361 eq854
    | exact resolve eq854 eq115361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116790 : (σ x) = (k (σ y) (k (σ x) (σ y))) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq115361 eq988
    | exact resolve eq988 eq115361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988 eq115361
  have eq116834 : (σ x) = (k (σ y) (k (σ x) (σ y))) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq116790
  have eq116835 : (σ x) = (M.op (k (σ x) (σ y)) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq116789
  have eq116874 : (σ x) = (k (σ x) (k (σ x) (σ x))) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq1617 eq116834
    | exact resolve eq116834 eq1617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1617 eq116834
  have eq116875 : (σ x) = (M.op (k (σ x) (σ x)) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq115363 eq116835
    | exact resolve eq116835 eq115363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116835
  have eq116949 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17648 eq116874
    | exact resolve eq116874 eq17648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116874
  have eq116950 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq116949
  have eq116951 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17648 eq116875
    | exact resolve eq116875 eq17648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17648 eq116875
  have eq116993 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq115363 eq116950
    | exact resolve eq116950 eq115363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116950
  have eq116994 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq115363 eq116951
    | exact resolve eq116951 eq115363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115363 eq116951
  have eq117217 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq116993 eq809
    | (have j0 := eq809 (σ x) X0
       grind)
    | (have r₁ := eq809 (σ x) x
       have r₂ := eq116993
       grind)
    | exact resolve eq809 eq116993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809 eq116993
  have eq117232 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq117217 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117217
  have eq117634 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq116994 eq854
    | exact resolve eq854 eq116994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854 eq116994
  have eq117716 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq117634
  have eq117750 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq117716
    | exact resolve eq117716 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117716
  have eq117819 : x = (k y y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq117750
       grind)
    | exact superpose eq117750 eq28
    | exact resolve eq28 eq117750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120245 : y = (k y x) ∨ y = (M.op y y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq822 y
       have i₂ := eq117819
       grind)
    | exact superpose eq117819 eq822
    | (have j0 := eq822 y
       grind)
    | exact resolve eq822 eq117819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117819
  have eq120268 : y = (k y x) ∨ x = y ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq117750 eq120245
    | exact resolve eq120245 eq117750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117750 eq120245
  have eq120269 : y = (k y x) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq120268
  have eq120547 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq120269
       grind)
    | exact superpose eq120269 eq40
    | exact resolve eq40 eq120269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120269
  have eq120565 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq120547
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq120547
    | exact resolve eq120547 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120547
  have eq120826 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq120565 eq803
    | exact resolve eq803 eq120565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120565
  have eq123172 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq117232 eq26
    | (have j1 := eq117232 (σ y)
       grind)
    | exact resolve eq26 eq117232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117232
  have eq123498 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq814 eq123172
    | exact resolve eq123172 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814 eq123172
  have eq123527 : x = (M.op y y) := by
    first
    | (have r₁ := eq123498
       have r₂ := eq27
       grind)
    | exact resolve eq123498 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123498
  have eq123585 : y = (M.op x x) := by
    first
    | (have i₁ := eq100025 y
       have i₂ := eq123527
       grind)
    | exact superpose eq123527 eq100025
    | exact resolve eq100025 eq123527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100025
  have eq123593 : x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq28 y y
       have i₂ := eq123527
       grind)
    | exact superpose eq123527 eq28
    | exact resolve eq28 eq123527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq123751 : y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq28 x x
       have i₂ := eq123585
       grind)
    | exact superpose eq123585 eq28
    | exact resolve eq28 eq123585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq123766 : ∀ X0 : G, x = (M.op (k x X0) y) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq768 x x x
       have i₂ := eq123585
       grind)
    | exact superpose eq123585 eq768
    | exact resolve eq768 eq123585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124291 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq41 y
       have i₂ := eq123593
       grind)
    | exact superpose eq123593 eq41
    | exact resolve eq41 eq123593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124302 : y = (k y x) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq822 y
       have i₂ := eq123593
       grind)
    | exact superpose eq123593 eq822
    | (have j0 := eq822 y
       grind)
    | exact resolve eq822 eq123593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123593
  have eq124324 : x = y ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq124302
       have i₂ := eq123527
       grind)
    | exact superpose eq123527 eq124302
    | exact resolve eq124302 eq123527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124302
  have eq124325 : y = (k y x) ∨ x = y := by grind
  clear eq124324
  have eq124326 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq124291
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq124291
    | exact resolve eq124291 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124291
  have eq124332 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq124326
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq124326
    | exact resolve eq124326 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124326
  have eq124366 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq123751
       grind)
    | exact superpose eq123751 eq40
    | exact resolve eq40 eq123751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124376 : x = (k x y) ∨ x = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq822 x
       have i₂ := eq123751
       grind)
    | exact superpose eq123751 eq822
    | (have j0 := eq822 x
       grind)
    | exact resolve eq822 eq123751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822 eq123751
  have eq124407 : x = y ∨ x = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq124376
       have i₂ := eq123585
       grind)
    | exact superpose eq123585 eq124376
    | exact resolve eq124376 eq123585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124376
  have eq124408 : x = (k x y) ∨ x = y := by grind
  clear eq124407
  have eq124409 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq124366
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq124366
    | exact resolve eq124366 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124366
  have eq124415 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq124409
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq124409
    | exact resolve eq124409 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124409
  have eq124428 : (σ y) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq124325
       grind)
    | exact superpose eq124325 eq40
    | exact resolve eq40 eq124325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq124325
  have eq124445 : (σ y) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq124428
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq124428
    | exact resolve eq124428 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124428
  have eq124482 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq124332 eq769
    | (have j0 := eq769 (σ y) (σ y) x
       grind)
    | exact resolve eq769 eq124332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124483 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq124332 eq768
    | (have j0 := eq768 (σ y) (σ y) x
       grind)
    | exact resolve eq768 eq124332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124332
  have eq124498 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq124408
       grind)
    | exact superpose eq124408 eq41
    | exact resolve eq41 eq124408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq124512 : (σ x) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq124498
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq124498
    | exact resolve eq124498 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124498
  have eq124547 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq124415 eq779
    | (have j0 := eq779 (σ x)
       grind)
    | exact resolve eq779 eq124415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124585 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq124415 eq768
    | (have j0 := eq768 (σ x) (σ x) x
       grind)
    | exact resolve eq768 eq124415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768 eq124415
  have eq124599 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq124445 eq803
    | exact resolve eq803 eq124445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq124627 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq124445 eq767
    | (have j0 := eq767 (σ y) (σ x) x
       grind)
    | exact resolve eq767 eq124445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767 eq124445
  have eq124637 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq124512 eq779
    | (have j0 := eq779 (σ y)
       grind)
    | exact resolve eq779 eq124512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq779
  have eq124641 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq124512 eq805
    | (have j0 := eq805 (σ x)
       grind)
    | exact resolve eq805 eq124512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq124650 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq124512 eq769
    | (have j0 := eq769 (σ x) (σ y) x
       grind)
    | exact resolve eq769 eq124512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769 eq124512
  have eq124654 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq124585 eq124650
    | (have j0 := eq124650 X0
       have j1 := eq124585 X0
       grind)
    | exact resolve eq124650 eq124585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124585 eq124650
  have eq126118 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq124599 eq178
    | exact resolve eq178 eq124599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq124599
  have eq126187 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ x) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq124654 eq126118
    | (have j0 := eq126118 X0
       have j1 := eq124654 X0
       grind)
    | exact resolve eq126118 eq124654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124654 eq126118
  have eq135861 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq124641 eq189
    | exact resolve eq189 eq124641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq124641
  have eq135945 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq124547 eq135861
    | exact resolve eq135861 eq124547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124547 eq135861
  have eq135952 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq135945 eq185
    | exact resolve eq185 eq135945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq135945
  have eq137378 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq124637 eq126187
    | exact resolve eq126187 eq124637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124637 eq126187
  have eq137492 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq137378
  have eq137504 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq120826 eq137492
    | exact resolve eq137492 eq120826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120826 eq137492
  have eq137505 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq26 eq137504
    | exact resolve eq137504 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137504
  have eq137506 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq137505
  have eq137550 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq137506 eq13681
    | exact resolve eq13681 eq137506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13681 eq137506
  have eq137661 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq12592 eq137550
    | exact resolve eq137550 eq12592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12592 eq137550
  have eq137665 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq55470 eq137661
    | exact resolve eq137661 eq55470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55470 eq137661
  have eq159589 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq124482 eq124483
    | exact resolve eq124483 eq124482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq159679 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq124483 eq124482
    | exact resolve eq124482 eq124483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124482
  have eq159686 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq124483 eq177
    | exact resolve eq177 eq124483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq124483
  have eq159755 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq159679
  have eq159784 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq159589
  have eq159797 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq124627 eq159686
    | (have j0 := eq159686 X0
       have j1 := eq124627 X0
       grind)
    | exact resolve eq159686 eq124627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124627 eq159686
  have eq159959 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq159755
  have eq160046 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq159784 eq34276
    | exact resolve eq34276 eq159784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159784
  have eq160235 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq55469 eq160046
    | exact resolve eq160046 eq55469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55469 eq160046
  have eq160243 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq137665 eq160235
    | exact resolve eq160235 eq137665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137665 eq160235
  have eq160244 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq160243
  have eq160405 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq135952 eq159797
    | exact resolve eq159797 eq135952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135952 eq159797
  have eq160523 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq160405
  have eq160563 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq160523
       have r₂ := eq159959
       grind)
    | exact resolve eq160523 eq159959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159959 eq160523
  have eq160629 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq160563 eq34276
    | exact resolve eq34276 eq160563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34276 eq160563
  have eq160795 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq160244 eq160629
    | exact resolve eq160629 eq160244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160244 eq160629
  have eq164180 : (M.op x y) = (τ (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq160795 eq29
    | exact resolve eq29 eq160795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160795
  have eq164394 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32 eq164180
    | exact resolve eq164180 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq164180
  have eq164395 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq164394
  have eq164418 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq164395 eq29
    | exact resolve eq29 eq164395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq164395
  have eq164667 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq164418
    | exact resolve eq164418 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq164418
  have eq164924 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq124408
       have i₂ := eq164667
       grind)
    | exact superpose eq164667 eq124408
    | exact resolve eq124408 eq164667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124408 eq164667
  have eq164933 : x = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq164924
  have eq165000 : x = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq164933
       have r₂ := eq67042
       grind)
    | exact resolve eq164933 eq67042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67042 eq164933
  have eq165109 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq165000 eq123766
    | (have j0 := eq123766 (M.op x y)
       grind)
    | exact resolve eq123766 eq165000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123766 eq165000
  have eq165182 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq165109
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq165109
    | exact resolve eq165109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165109
  have eq165183 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq165182
  have eq165208 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq165183
       grind)
    | exact superpose eq165183 eq18
    | exact resolve eq18 eq165183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165433 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq123527
       have i₂ := eq165183
       grind)
    | exact superpose eq165183 eq123527
    | exact resolve eq123527 eq165183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123527
  have eq165895 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq165208 eq197
    | exact resolve eq197 eq165208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq165208
  have eq166018 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq165183 eq165895
    | exact resolve eq165895 eq165183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165183 eq165895
  have eq166683 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq166018 eq165433
    | exact resolve eq165433 eq166018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165433 eq166018
  have eq166842 : x = (M.op x y) := by grind
  clear eq166683
  have eq166869 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq166842
       grind)
    | exact superpose eq166842 eq18
    | exact resolve eq18 eq166842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq166870 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq166842
       grind)
    | exact superpose eq166842 eq22
    | exact resolve eq22 eq166842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq167172 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq123585
       have i₂ := eq166842
       grind)
    | exact superpose eq166842 eq123585
    | exact resolve eq123585 eq166842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123585
  have eq167361 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq166870 eq20
    | exact resolve eq20 eq166870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq167953 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq166869 eq207
    | exact resolve eq207 eq166869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207 eq166869
  have eq168104 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq167953
       have i₂ := eq166842
       grind)
    | exact superpose eq166842 eq167953
    | exact resolve eq167953 eq166842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166842 eq167953
  have eq168447 : y = (M.op x y) := by
    first
    | exact superpose eq168104 eq167172
    | exact resolve eq167172 eq168104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167172
  have eq168524 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq168104 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq168104
       grind)
    | exact resolve eq13 eq168104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq168593 : ∀ X0 : G, (k X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have j0 := eq168524 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168524
  have eq168617 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq168447
       grind)
    | exact superpose eq168447 eq24
    | exact resolve eq24 eq168447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq168447
  have eq168984 : (σ x) = (σ y) := by
    first
    | exact superpose eq166870 eq168617
    | exact resolve eq168617 eq166870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166870 eq168617
  have eq169097 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq168984 eq26
    | exact resolve eq26 eq168984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq168984
  have eq171933 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq168593 eq168104
    | exact resolve eq168104 eq168593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168104 eq168593
  have eq172412 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq171933 eq38
    | exact resolve eq38 eq171933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq172462 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq171933 eq1198
    | (have j0 := eq1198 (M.op x y) X0
       grind)
    | exact resolve eq1198 eq171933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198 eq171933
  have eq172471 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq172462 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172462
  have eq172485 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq20 eq172471
    | (have j0 := eq172471 X0
       grind)
    | exact resolve eq172471 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172471
  have eq172488 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq172412
    | exact resolve eq172412 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq172412
  have eq172491 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq167361 eq172485
    | exact resolve eq172485 eq167361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172485
  have eq172494 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq167361 eq172488
    | exact resolve eq172488 eq167361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172488
  have eq173590 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq172491 eq169097
    | exact resolve eq169097 eq172491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169097 eq172491
  have eq173903 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq172494 eq173590
    | exact resolve eq173590 eq172494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172494 eq173590
  have eq174022 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq173903 eq27
    | exact resolve eq27 eq173903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq173903
  have eq174192 : False := by grind
  exact eq174192

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  clear eq17
  have eq23 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq45 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq45 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq84 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) X0
       have i₂ := eq46 (σ X0)
       grind)
    | exact superpose eq46 eq22
    | exact resolve eq22 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq85 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq46 (τ X0)
       grind)
    | exact superpose eq46 eq18
    | exact resolve eq18 eq46
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
  have eq87 : ∀ X0 : G, (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq94 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq86
    | exact resolve eq86 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq95 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq87 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq87
    | exact resolve eq87 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq87
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
  have eq109 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq23 X2 X0 x
       grind)
    | exact superpose eq23 eq23
    | exact resolve eq23 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq166 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
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
  have eq192 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X1 (σ X0) (σ X0)
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq23
    | exact resolve eq23 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) (σ X0) X1
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq23
    | exact resolve eq23 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) (σ X0) x
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq24
    | exact resolve eq24 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq715 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq166
       have i₂ := eq59 y x
       grind)
    | exact superpose eq59 eq166
    | (have j1 := eq59 (σ y) (σ x)
       grind)
    | exact resolve eq166 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq166
  have eq716 : (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq715
  have eq3514 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x y) X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq24 y x x
       have i₂ := eq716
       grind)
    | exact superpose eq716 eq24
    | exact resolve eq24 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3522 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq109 x x y
       have i₂ := eq716
       grind)
    | exact superpose eq716 eq109
    | exact resolve eq109 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq39403 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3514 (M.op y x)
       have i₂ := eq23 x y x
       grind)
    | exact superpose eq23 eq3514
    | exact resolve eq3514 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3514
  have eq39837 : (σ y) = (M.op (σ (M.op y y)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq193 y (σ x)
       have i₂ := eq39403
       grind)
    | exact superpose eq39403 eq193
    | exact resolve eq193 eq39403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40234 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq109 (σ y) (σ (M.op y y)) (σ x)
       have i₂ := eq39837
       grind)
    | exact superpose eq39837 eq109
    | exact resolve eq109 eq39837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq39837
  have eq40281 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq40234
       have i₂ := eq98 y
       grind)
    | exact superpose eq98 eq40234
    | exact resolve eq40234 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40234
  have eq40695 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (σ x) (σ y)
       have i₂ := eq40281
       grind)
    | exact superpose eq40281 eq23
    | exact resolve eq23 eq40281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40281
  have eq41935 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq40695 (σ y)
       have i₂ := eq39403
       grind)
    | exact superpose eq39403 eq40695
    | exact resolve eq40695 eq39403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39403 eq40695
  have eq42004 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq41935
  have eq42026 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq42004
       have i₂ := eq192 y (σ x)
       grind)
    | exact superpose eq192 eq42004
    | exact resolve eq42004 eq192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42004
  have eq42433 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (σ y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq192 y X0
       have i₂ := eq42026
       grind)
    | exact superpose eq42026 eq192
    | exact resolve eq192 eq42026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43785 : (σ y) = (M.op (σ (M.op y y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq42433 (σ y)
       have i₂ := eq98 y
       grind)
    | exact superpose eq98 eq42433
    | exact resolve eq42433 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42433
  have eq46581 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq43785
       have i₂ := eq42026
       grind)
    | exact superpose eq42026 eq43785
    | exact resolve eq43785 eq42026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42026 eq43785
  have eq46637 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) := by grind
  clear eq46581
  have eq46662 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq46637
       have i₂ := eq98 (M.op x y)
       grind)
    | exact superpose eq98 eq46637
    | exact resolve eq46637 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46637
  have eq46681 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq46662
       grind)
    | exact superpose eq46662 eq10
    | exact resolve eq10 eq46662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46662
  have eq46937 : x = y ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq46681
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq46681
    | exact resolve eq46681 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46681
  have eq47177 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq16
       have i₂ := eq46937
       grind)
    | exact superpose eq46937 eq16
    | exact resolve eq16 eq46937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46937
  have eq47178 : (σ y) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have r₁ := eq47177
       have r₂ := eq98 x
       grind)
    | exact resolve eq47177 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47177
  have eq47200 : (M.op (M.op x y) (M.op x y)) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op (M.op x y) (M.op x y))
       have i₂ := eq47178
       grind)
    | exact superpose eq47178 eq10
    | exact resolve eq10 eq47178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47217 : (τ (M.op (σ y) (σ y))) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq95 (M.op (M.op x y) (M.op x y))
       have i₂ := eq47178
       grind)
    | exact superpose eq47178 eq95
    | exact resolve eq95 eq47178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47471 : (M.op x y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq47217
       have i₂ := eq9 (M.op x y) x y (M.op x y)
       grind)
    | exact superpose eq9 eq47217
    | exact resolve eq47217 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47217
  have eq47484 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq47200
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq47200
    | exact resolve eq47200 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47200
  have eq47486 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq47471
       have i₂ := eq95 y
       grind)
    | exact superpose eq95 eq47471
    | exact resolve eq47471 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq47471
  have eq118634 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq3522 (M.op x x)
       have i₂ := eq23 x x y
       grind)
    | exact superpose eq23 eq3522
    | exact resolve eq3522 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3522
  have eq118772 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x x))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq192 x (σ y)
       have i₂ := eq118634
       grind)
    | exact superpose eq118634 eq192
    | exact resolve eq192 eq118634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq118912 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq24 (σ x) (σ y) (σ (M.op x x))
       have i₂ := eq118772
       grind)
    | exact superpose eq118772 eq24
    | exact resolve eq24 eq118772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq118772
  have eq119047 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq118912
       have i₂ := eq98 x
       grind)
    | exact superpose eq98 eq118912
    | exact resolve eq118912 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118912
  have eq119141 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq23 (σ x) (σ y) X0
       have i₂ := eq119047
       grind)
    | exact superpose eq119047 eq23
    | exact resolve eq23 eq119047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119047
  have eq119318 : ∀ X0 : G, y = (M.op (M.op x x) (M.op x x)) ∨ (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47484
       have i₂ := eq119141 X0
       grind)
    | exact superpose eq119141 eq47484
    | (have j1 := eq119141 X0
       grind)
    | exact resolve eq47484 eq119141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47484 eq119141
  have eq119434 : ∀ X0 : G, x = y ∨ (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq119318 X0
       have i₂ := eq23 x x x
       grind)
    | (have i₁ := eq119318 X0
       have i₂ := eq23 X0 (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq23 eq119318
    | (have j0 := eq119318 X0
       grind)
    | exact resolve eq119318 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119318
  have eq119437 : ∀ X0 : G, (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq119434 X0
       grind)
    | exact superpose eq119434 eq16
    | (have j1 := eq119434 X0
       grind)
    | exact resolve eq16 eq119434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119434
  have eq119483 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have j0 := eq119437 X0
       grind)
    | (have r₁ := eq119437 X0
       have r₂ := eq98 x
       grind)
    | exact resolve eq119437 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119437
  have eq119497 : (σ y) = (M.op (σ (M.op x x)) (M.op (σ x) (σ y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq119483 (σ x)
       have i₂ := eq118634
       grind)
    | exact superpose eq118634 eq119483
    | exact resolve eq119483 eq118634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118634
  have eq119518 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq194 x (M.op (σ y) x)
       have i₂ := eq119483 x
       grind)
    | exact superpose eq119483 eq194
    | exact resolve eq194 eq119483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194 eq119483
  have eq119666 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq119497
       have i₂ := eq193 x (σ y)
       grind)
    | exact superpose eq193 eq119497
    | exact resolve eq119497 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193 eq119497
  have eq119699 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq119518
       grind)
    | exact superpose eq119518 eq16
    | exact resolve eq16 eq119518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119518
  have eq120102 : (σ y) = (σ (M.op (M.op x x) (M.op x x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq47178
       have i₂ := eq119666
       grind)
    | exact superpose eq119666 eq47178
    | exact resolve eq47178 eq119666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47178 eq119666
  have eq120251 : (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq120102
       have i₂ := eq23 x x x
       grind)
    | (have i₁ := eq120102
       have i₂ := eq23 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq23 eq120102
    | exact resolve eq120102 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq120102
  have eq120252 : (σ x) = (σ y) := by grind
  clear eq120251
  have eq120299 : (σ (M.op y y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq98 y
       have i₂ := eq120252
       grind)
    | exact superpose eq120252 eq98
    | exact resolve eq98 eq120252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120252
  have eq120769 : (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq120299
       have i₂ := eq98 x
       grind)
    | exact superpose eq98 eq120299
    | exact resolve eq120299 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq120299
  have eq120785 : (σ (M.op x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq120769
       have i₂ := eq47486
       grind)
    | exact superpose eq47486 eq120769
    | exact resolve eq120769 eq47486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47486 eq120769
  have eq120786 : False := by grind
  exact eq120786

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq9 X0 x x X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq19 X0 X0 X0
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
    | (have i₁ := eq32 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq79 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq17
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq17 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (k (τ X0) X1) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq32
    | (have j1 := eq14 (σ X1) (σ X1)
       grind)
    | exact resolve eq32 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq180 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
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
  have eq184 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (M.op X2 (σ X0)) (σ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 (σ X0) (σ X1)
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq19
    | (have j1 := eq77 X1 X1
       grind)
    | exact resolve eq19 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (σ X0) (σ X1) X2
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq19
    | (have j1 := eq77 X1 X1
       grind)
    | exact resolve eq19 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq195 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq194 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq276 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq195 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq195
    | (have j0 := eq195 (τ X0)
       grind)
    | exact resolve eq195 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq278 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq276 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq276
    | (have j0 := eq276 X0
       grind)
    | exact resolve eq276 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq281 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq278 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq278
    | (have j0 := eq278 X0
       grind)
    | exact resolve eq278 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq287 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq281 (τ X0)
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq281
    | (have j0 := eq281 (τ X0)
       grind)
    | exact resolve eq281 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq406 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq79
    | (have j0 := eq79 X0 X1
       grind)
    | exact resolve eq79 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq438 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq406 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq406
    | (have j0 := eq406 X0 X1
       grind)
    | exact resolve eq406 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq944 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq945 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq944 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq1160 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq185 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq1161 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1160 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq2256 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X1 X0) (σ (k (τ X0) (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq945 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq945
    | exact resolve eq945 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq2296 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k (σ (τ X0)) X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2256 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2256
    | (have j0 := eq2256 X0 X1
       grind)
    | exact resolve eq2256 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2256
  have eq2297 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2296 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2296
    | (have j0 := eq2296 X0 X1
       grind)
    | exact resolve eq2296 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2296
  have eq2374 : ∀ X0 X2 : G, (k X0 X0) = (M.op X0 (M.op (k X0 X0) X2)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq19 (M.op x X0) (k X0 X0) X2
       have i₂ := eq2297 X0 x
       grind)
    | exact superpose eq2297 eq19
    | (have j1 := eq2297 X0 x
       grind)
    | exact resolve eq19 eq2297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2297
  have eq2419 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (σ (k (τ X0) (τ X0))) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1161 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1161
    | exact resolve eq1161 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161
  have eq2459 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2419 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2419
    | (have j0 := eq2419 X0 X1
       grind)
    | exact resolve eq2419 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2419
  have eq2460 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2459 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2459
    | (have j0 := eq2459 X0 X1
       grind)
    | exact resolve eq2459 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2459
  have eq2474 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2374 X0 (M.op X0 x)
       have i₂ := eq2460 X0 x
       grind)
    | exact superpose eq2460 eq2374
    | (have j0 := eq2374 X0 x
       have j1 := eq2460 X0 x
       grind)
    | exact resolve eq2374 eq2460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2374 eq2460
  have eq2489 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2474 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2474
  have eq2492 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2489 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq2489 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq2489 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2489
  have eq2501 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq287 X0
       have i₂ := eq2492 X0
       grind)
    | exact superpose eq2492 eq287
    | (have j0 := eq287 X0
       grind)
    | exact resolve eq287 eq2492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq2510 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq193 X0 X0
       have i₂ := eq2492 X0
       grind)
    | exact superpose eq2492 eq193
    | (have j0 := eq193 X0 X0
       grind)
    | exact resolve eq193 eq2492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq2532 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2492 (σ X0)
       grind)
    | exact superpose eq2492 eq15
    | exact resolve eq15 eq2492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2540 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0 X0
       have i₂ := eq2492 (τ X0)
       grind)
    | exact superpose eq2492 eq43
    | exact resolve eq43 eq2492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq2562 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2510 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2510
  have eq2583 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2540 X0
       have i₂ := eq2492 X0
       grind)
    | exact superpose eq2492 eq2540
    | exact resolve eq2540 eq2492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2540
  have eq2590 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2532 X0
       have i₂ := eq2492 X0
       grind)
    | exact superpose eq2492 eq2532
    | exact resolve eq2532 eq2492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2492 eq2532
  have eq2824 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (σ X0) X1
       have i₂ := eq2590 X0
       grind)
    | exact superpose eq2590 eq34
    | exact resolve eq34 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4074 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (M.op X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2501 (σ X0)
       have i₂ := eq82 X1 X0
       grind)
    | exact superpose eq82 eq2501
    | (have j0 := eq2501 (σ X0)
       have j1 := eq82 X1 X0
       grind)
    | exact resolve eq2501 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq4099 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (M.op X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq4074 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4074
  have eq4109 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4099 X0 X1
       have i₂ := eq2583 (σ X0)
       grind)
    | exact superpose eq2583 eq4099
    | (have j0 := eq4099 X0 X1
       grind)
    | exact resolve eq4099 eq2583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4099
  have eq4114 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (M.op X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4109 X0 X1
       have i₂ := eq2590 X0
       grind)
    | exact superpose eq2590 eq4109
    | (have j0 := eq4109 X0 X1
       grind)
    | exact resolve eq4109 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4109
  have eq4116 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (M.op X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4114 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq4114
    | (have j0 := eq4114 X0 X1
       grind)
    | exact resolve eq4114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4114
  have eq4118 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op X1 (σ X0))) ∨ (M.op X1 (σ X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4116 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4116
    | (have j0 := eq4116 X0 X1
       grind)
    | exact resolve eq4116 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4116
  have eq14846 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 (σ X1))
       have i₂ := eq4118 X1 X0
       grind)
    | exact superpose eq4118 eq11
    | (have j1 := eq4118 X1 X0
       grind)
    | exact resolve eq11 eq4118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4118
  have eq14939 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14846 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq14846
    | (have j0 := eq14846 X0 X1
       grind)
    | exact resolve eq14846 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14846
  have eq15064 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14939 (σ X0) X1
       grind)
    | exact superpose eq14939 eq15
    | (have j1 := eq14939 (σ X0) X1
       grind)
    | exact resolve eq15 eq14939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14939
  have eq32805 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15064 x y
       grind)
    | exact superpose eq15064 eq16
    | (have j1 := eq15064 x y
       grind)
    | exact resolve eq16 eq15064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15064
  have eq33870 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq32805
       have i₂ := eq438 x y
       grind)
    | exact superpose eq438 eq32805
    | (have j1 := eq438 y y
       grind)
    | (have r₁ := eq32805
       have r₂ := eq438 x y
       grind)
    | exact resolve eq32805 eq438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438 eq32805
  have eq33871 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq33870
  have eq33872 : x = (M.op x y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq33871
  have eq34009 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19 X0 x y
       have i₂ := eq33872
       grind)
    | exact superpose eq33872 eq19
    | exact resolve eq19 eq33872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq33872
  have eq34036 : x = (M.op x x) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq34009 (M.op x x)
       have i₂ := eq34009 x
       grind)
    | exact superpose eq34009 eq34009
    | exact resolve eq34009 eq34009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34009
  have eq34078 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq34036
  have eq34302 : ∀ X0 : G, y = (M.op y y) ∨ (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq20 (σ x) (σ y) x
       have i₂ := eq34078
       grind)
    | exact superpose eq34078 eq20
    | exact resolve eq20 eq34078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq34078
  have eq35817 : ∀ X0 : G, (τ y) ≠ (τ y) ∨ (τ y) = (M.op (τ y) (τ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq2501 y
       have i₂ := eq34302 X0
       grind)
    | exact superpose eq34302 eq2501
    | (have j0 := eq2501 y
       have j1 := eq34302 X0
       grind)
    | exact resolve eq2501 eq34302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34302
  have eq35883 : ∀ X0 : G, (τ y) = (M.op (τ y) (τ y)) ∨ (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq35817 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35817
  have eq35891 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ (τ y) = (τ (M.op y y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq35883 X0
       have i₂ := eq2583 y
       grind)
    | exact superpose eq2583 eq35883
    | (have j0 := eq35883 X0
       grind)
    | exact resolve eq35883 eq2583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35883
  have eq39137 : (σ x) = (M.op (σ x) (σ x)) ∨ (τ y) = (τ (M.op y y)) ∨ x = (M.op x x) ∨ (τ y) = (τ (M.op y y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq35891 (M.op (σ x) x)
       have i₂ := eq35891 x
       grind)
    | exact superpose eq35891 eq35891
    | exact resolve eq35891 eq35891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35891
  have eq39204 : (σ x) = (M.op (σ x) (σ x)) ∨ (τ y) = (τ (M.op y y)) ∨ x = (M.op x x) := by grind
  clear eq39137
  have eq39219 : x = (M.op x x) ∨ (τ y) = (τ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq39204
       have i₂ := eq2590 x
       grind)
    | exact superpose eq2590 eq39204
    | exact resolve eq39204 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39204
  have eq39492 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (τ y) = (τ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2562 x
       have i₂ := eq39219
       grind)
    | exact superpose eq39219 eq2562
    | (have j0 := eq2562 x
       grind)
    | (have r₁ := eq2562 x
       have r₂ := eq39219
       grind)
    | exact resolve eq2562 eq39219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39219
  have eq39552 : (σ x) = (M.op (σ x) (σ x)) ∨ (τ y) = (τ (M.op y y)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq39492
  have eq39564 : (σ x) = (M.op (σ x) (σ x)) ∨ (τ y) = (τ (M.op y y)) := by
    first
    | (have j1 := eq2562 x
       grind)
    | (have r₁ := eq39552
       have r₂ := eq2562 x
       grind)
    | exact resolve eq39552 eq2562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39552
  have eq39569 : (σ x) = (σ (M.op x x)) ∨ (τ y) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq39564
       have i₂ := eq2590 x
       grind)
    | exact superpose eq2590 eq39564
    | exact resolve eq39564 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39564
  have eq39598 : (M.op x x) = (τ (σ x)) ∨ (τ y) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq39569
       grind)
    | exact superpose eq39569 eq10
    | exact resolve eq10 eq39569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39569
  have eq39789 : x = (M.op x x) ∨ (τ y) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq39598
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq39598
    | exact resolve eq39598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39598
  have eq40054 : (τ x) ≠ (τ x) ∨ (τ x) = (M.op (τ x) (τ x)) ∨ (τ y) = (τ (M.op y y)) := by
    first
    | (have i₁ := eq2501 x
       have i₂ := eq39789
       grind)
    | exact superpose eq39789 eq2501
    | (have j0 := eq2501 x
       grind)
    | (have r₁ := eq2501 y
       have r₂ := eq39789
       grind)
    | exact resolve eq2501 eq39789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2501 eq39789
  have eq40120 : (τ x) = (M.op (τ x) (τ x)) ∨ (τ y) = (τ (M.op y y)) := by grind
  clear eq40054
  have eq40129 : (τ y) = (τ (M.op y y)) ∨ (τ x) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq40120
       have i₂ := eq2583 x
       grind)
    | exact superpose eq2583 eq40120
    | exact resolve eq40120 eq2583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2583 eq40120
  have eq40800 : (M.op y y) = (σ (τ y)) ∨ (τ x) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq11 (M.op y y)
       have i₂ := eq40129
       grind)
    | exact superpose eq40129 eq11
    | exact resolve eq11 eq40129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40129
  have eq41027 : y = (M.op y y) ∨ (τ x) = (τ (M.op x x)) := by
    first
    | (have i₁ := eq40800
       have i₂ := eq11 y
       grind)
    | exact superpose eq11 eq40800
    | exact resolve eq40800 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40800
  have eq41045 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ (τ x) = (τ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq34 y x
       have i₂ := eq41027
       grind)
    | exact superpose eq41027 eq34
    | (have r₁ := eq34 y x
       have r₂ := eq41027
       grind)
    | exact resolve eq34 eq41027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41058 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (τ x) = (τ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq2824 y x
       have i₂ := eq41027
       grind)
    | exact superpose eq41027 eq2824
    | exact resolve eq2824 eq41027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41027
  have eq41109 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (τ x) = (τ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq41058 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41058
  have eq41117 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ (τ x) = (τ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq41045 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41045
  have eq41699 : ∀ X0 : G, (τ x) = (τ (M.op x x)) ∨ (k X0 (σ y)) = (σ (M.op (τ X0) y)) := by
    intro X0
    first
    | (have i₁ := eq17 X0 y
       have i₂ := eq41117 (τ X0)
       grind)
    | exact superpose eq41117 eq17
    | exact resolve eq17 eq41117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq41117
  have eq46066 : ∀ X0 : G, (τ x) = (τ (M.op x x)) ∨ (M.op (σ X0) (σ y)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq41109 (σ X0)
       grind)
    | exact superpose eq41109 eq15
    | exact resolve eq15 eq41109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41109
  have eq64128 : ∀ X0 : G, (M.op x x) = (σ (τ x)) ∨ (k X0 (σ y)) = (σ (M.op (τ X0) y)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op x x)
       have i₂ := eq41699 X0
       grind)
    | exact superpose eq41699 eq11
    | (have j1 := eq41699 X0
       grind)
    | exact resolve eq11 eq41699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41699
  have eq64380 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (σ y)) = (σ (M.op (τ X0) y)) := by
    intro X0
    first
    | (have i₁ := eq64128 X0
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq64128
    | (have j0 := eq64128 X0
       grind)
    | exact resolve eq64128 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64128
  have eq64893 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = (σ (M.op (τ X0) y)) := by
    intro X0
    first
    | (have i₁ := eq2562 x
       have i₂ := eq64380 X0
       grind)
    | exact superpose eq64380 eq2562
    | (have j0 := eq2562 x
       have j1 := eq64380 X0
       grind)
    | exact resolve eq2562 eq64380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64380
  have eq64953 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (k X0 (σ y)) = (σ (M.op (τ X0) y)) := by
    intro X0
    first
    | (have j0 := eq64893 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64893
  have eq64964 : ∀ X0 : G, (k X0 (σ y)) = (σ (M.op (τ X0) y)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq64953 X0
       have i₂ := eq2590 x
       grind)
    | exact superpose eq2590 eq64953
    | (have j0 := eq64953 X0
       grind)
    | exact resolve eq64953 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64953
  have eq65876 : ∀ X0 : G, (M.op x x) = (σ (τ x)) ∨ (M.op (σ X0) (σ y)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op x x)
       have i₂ := eq46066 X0
       grind)
    | exact superpose eq46066 eq11
    | (have j1 := eq46066 X0
       grind)
    | exact resolve eq11 eq46066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46066
  have eq66128 : ∀ X0 : G, x = (M.op x x) ∨ (M.op (σ X0) (σ y)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq65876 X0
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq65876
    | (have j0 := eq65876 X0
       grind)
    | exact resolve eq65876 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65876
  have eq66540 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ X0) (σ y)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq2562 x
       have i₂ := eq66128 X0
       grind)
    | exact superpose eq66128 eq2562
    | (have j0 := eq2562 x
       have j1 := eq66128 X0
       grind)
    | exact resolve eq2562 eq66128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66128
  have eq66600 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ X0) (σ y)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have j0 := eq66540 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66540
  have eq66611 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 y)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq66600 X0
       have i₂ := eq2590 x
       grind)
    | exact superpose eq2590 eq66600
    | (have j0 := eq66600 X0
       grind)
    | exact resolve eq66600 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66600
  have eq71933 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (M.op X0 y)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq64964 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq64964
    | exact resolve eq64964 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64964
  have eq72176 : ∀ X0 : G, (σ (k X0 y)) = (σ (M.op X0 y)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq71933 X0
       have i₂ := eq15 X0 y
       grind)
    | exact superpose eq15 eq71933
    | exact resolve eq71933 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71933
  have eq84593 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66611 x
       grind)
    | exact superpose eq66611 eq16
    | exact resolve eq16 eq66611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66611
  have eq84800 : (σ x) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq84593
       have r₂ := eq72176 x
       grind)
    | exact resolve eq84593 eq72176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72176 eq84593
  have eq85639 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq84800
       grind)
    | exact superpose eq84800 eq10
    | exact resolve eq10 eq84800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85651 : ∀ X0 : G, (k (M.op x x) (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq40 (M.op x x) X0
       have i₂ := eq84800
       grind)
    | exact superpose eq84800 eq40
    | exact resolve eq40 eq84800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85965 : ∀ X0 : G, (k (M.op x x) (τ X0)) = (k x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq85651 X0
       have i₂ := eq40 x X0
       grind)
    | exact superpose eq40 eq85651
    | exact resolve eq85651 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq85651
  have eq85977 : x = (M.op x x) := by
    first
    | (have i₁ := eq85639
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq85639
    | exact resolve eq85639 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85639
  have eq94509 : ∀ X0 : G, (k x (τ X0)) = (M.op (M.op x x) (τ X0)) ∨ (M.op x x) = (M.op (M.op x x) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op x x) (τ X0)
       have i₂ := eq85965 X0
       grind)
    | exact superpose eq85965 eq14
    | (have j0 := eq14 (M.op x x) (τ X0)
       grind)
    | exact resolve eq14 eq85965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85965
  have eq94582 : ∀ X0 : G, (k x (τ X0)) = (M.op x (τ X0)) ∨ (M.op x x) = (M.op (M.op x x) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq94509 X0
       have i₂ := eq85977
       grind)
    | exact superpose eq85977 eq94509
    | (have j0 := eq94509 X0
       grind)
    | exact resolve eq94509 eq85977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94509
  have eq94650 : ∀ X0 : G, (k x (τ X0)) = (M.op x (τ X0)) ∨ (M.op x x) = (M.op (M.op x x) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq94582 X0
       have j1 := eq12 x (τ X0)
       grind)
    | (have r₁ := eq94582 X0
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq94582 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94582
  have eq94678 : ∀ X0 : G, x = (M.op x (τ X0)) ∨ (k x (τ X0)) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq94650 X0
       have i₂ := eq85977
       grind)
    | exact superpose eq85977 eq94650
    | (have j0 := eq94650 X0
       grind)
    | exact resolve eq94650 eq85977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94650
  have eq141555 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ x = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq94678 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq94678
    | exact resolve eq94678 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141658 : ∀ X0 : G, x ≠ x ∨ (M.op x x) = (k x (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k x (τ X0)) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq13 x (τ X0)
       have i₂ := eq94678 X0
       grind)
    | exact superpose eq94678 eq13
    | (have j0 := eq13 x (τ X0)
       have j1 := eq94678 X0
       grind)
    | (have r₁ := eq13 x (τ X0)
       have r₂ := eq94678 X0
       grind)
    | exact resolve eq13 eq94678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94678
  have eq141684 : ∀ X0 : G, (M.op x x) = (k x (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (k x (τ X0)) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have j0 := eq141658 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141658
  have eq141689 : ∀ X0 : G, (M.op x x) = (k x (τ X0)) ∨ (k x (τ X0)) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have j0 := eq141684 X0
       have j1 := eq12 x (τ X0)
       grind)
    | (have r₁ := eq141684 X0
       have r₂ := eq12 X0 (τ X0)
       grind)
    | exact resolve eq141684 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141684
  have eq141695 : ∀ X0 : G, x = (k x (τ X0)) ∨ (k x (τ X0)) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq141689 X0
       have i₂ := eq85977
       grind)
    | exact superpose eq85977 eq141689
    | (have j0 := eq141689 X0
       grind)
    | exact resolve eq141689 eq85977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85977 eq141689
  have eq150085 : ∀ X0 : G, x ≠ (M.op x (τ X0)) ∨ (k x (τ X0)) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have j0 := eq141695 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141695
  have eq150099 : ∀ X0 : G, (k x (τ X0)) = (M.op x (τ X0)) := by
    intro X0
    first
    | (have j0 := eq150085 X0
       have j1 := eq141555 (τ X0)
       grind)
    | (have r₁ := eq150085 X0
       have r₂ := eq141555 (τ X0)
       grind)
    | exact resolve eq150085 eq141555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141555 eq150085
  have eq150126 : ∀ X0 : G, (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq150099 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq150099
    | exact resolve eq150099 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150099
  have eq150965 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq180
       have i₂ := eq150126 y
       grind)
    | exact superpose eq150126 eq180
    | exact resolve eq180 eq150126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq151110 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq150965
  have eq151149 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq151110
       have i₂ := eq2590 y
       grind)
    | exact superpose eq2590 eq151110
    | exact resolve eq151110 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151110
  have eq200464 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq151149
       grind)
    | exact superpose eq151149 eq16
    | exact resolve eq16 eq151149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200513 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq151149
       grind)
    | exact superpose eq151149 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq151149
       grind)
    | exact resolve eq13 eq151149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151149
  have eq200540 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq200513
  have eq200546 : (M.op (σ x) (σ x)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq2562 y
       grind)
    | (have r₁ := eq200540
       have r₂ := eq2562 y
       grind)
    | exact resolve eq200540 eq2562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2562 eq200540
  have eq200564 : (σ (k x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq200546
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq200546
    | exact resolve eq200546 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200546
  have eq200569 : (σ (k x y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq200564
       have i₂ := eq2590 x
       grind)
    | exact superpose eq2590 eq200564
    | exact resolve eq200564 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200564
  have eq200571 : (σ x) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq200569
       have i₂ := eq84800
       grind)
    | exact superpose eq84800 eq200569
    | exact resolve eq200569 eq84800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84800 eq200569
  have eq200572 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq200571
       have i₂ := eq150126 y
       grind)
    | exact superpose eq150126 eq200571
    | exact resolve eq200571 eq150126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150126 eq200571
  have eq200573 : (σ y) = (σ (M.op y y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq200572
       have i₂ := eq2590 y
       grind)
    | exact superpose eq2590 eq200572
    | exact resolve eq200572 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2590 eq200572
  have eq200574 : (σ y) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq200573
       have r₂ := eq200464
       grind)
    | exact resolve eq200573 eq200464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200464 eq200573
  have eq200589 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq2824 y x
       have i₂ := eq200574
       grind)
    | exact superpose eq200574 eq2824
    | (have r₁ := eq2824 y x
       have r₂ := eq200574
       grind)
    | exact resolve eq2824 eq200574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824
  have eq200611 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq200574
       grind)
    | exact superpose eq200574 eq10
    | exact resolve eq10 eq200574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200574
  have eq200886 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq200589 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200589
  have eq201054 : y = (M.op y y) := by
    first
    | (have i₁ := eq200611
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq200611
    | exact resolve eq200611 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200611
  have eq202654 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq34 y x
       have i₂ := eq201054
       grind)
    | exact superpose eq201054 eq34
    | (have r₁ := eq34 y x
       have r₂ := eq201054
       grind)
    | exact resolve eq34 eq201054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq201054
  have eq202744 : ∀ X0 : G, (k X0 y) = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq202654 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202654
  have eq206479 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (k X0 y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq200886 (σ X0)
       grind)
    | exact superpose eq200886 eq15
    | exact resolve eq15 eq200886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200886
  have eq206758 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq206479 X0
       have i₂ := eq202744 X0
       grind)
    | exact superpose eq202744 eq206479
    | exact resolve eq206479 eq202744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202744 eq206479
  have eq215494 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq206758 x
       grind)
    | exact superpose eq206758 eq16
    | (have r₁ := eq16
       have r₂ := eq206758 x
       grind)
    | exact resolve eq16 eq206758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206758
  have eq215683 : False := by grind
  exact eq215683

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_pyy_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq61 X0 X0 X0
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq338 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq342 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq339 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq339 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq339 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq357 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq376 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq357 X0
       have i₂ := eq342 X0
       grind)
    | exact superpose eq342 eq357
    | exact resolve eq357 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq357
  have eq422 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0) (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq61
    | exact resolve eq61 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq428 X0 X1
       have j1 := eq430 X0 X1
       grind)
    | (have r₁ := eq428 X0 X1
       have r₂ := eq430 X0 X1
       grind)
    | exact resolve eq428 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq1061 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq431 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq431
    | exact resolve eq431 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1072 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq431 X1 (σ X0)
       grind)
    | exact superpose eq431 eq15
    | (have j1 := eq431 X1 (σ X0)
       grind)
    | exact resolve eq15 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq1112 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq1061 X1 (τ X0)
       grind)
    | exact superpose eq1061 eq17
    | (have j1 := eq1061 X1 (τ X0)
       grind)
    | exact resolve eq17 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1061
  have eq1314 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1112 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1112
    | exact resolve eq1112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112
  have eq1382 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1314 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1314
    | (have j0 := eq1314 X0 X1
       grind)
    | exact resolve eq1314 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314
  have eq1888 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1072 x y
       grind)
    | exact superpose eq1072 eq16
    | (have j1 := eq1072 x y
       grind)
    | exact resolve eq16 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq2098 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1888
       have i₂ := eq1382 x y
       grind)
    | exact superpose eq1382 eq1888
    | (have j1 := eq1382 (σ x) (σ y)
       grind)
    | (have r₁ := eq1888
       have r₂ := eq1382 x y
       grind)
    | exact resolve eq1888 eq1382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888
  have eq2099 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2098
  have eq2105 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61 x y X0
       have i₂ := eq2099
       grind)
    | exact superpose eq2099 eq61
    | exact resolve eq61 eq2099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099
  have eq2177 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2105 (M.op y x)
       have i₂ := eq2105 x
       grind)
    | exact superpose eq2105 eq2105
    | exact resolve eq2105 eq2105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2105
  have eq2192 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2177
  have eq2194 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2192
       grind)
    | exact superpose eq2192 eq16
    | exact resolve eq16 eq2192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2196 : (σ y) = (M.op (σ y) (σ (M.op y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq422 y (σ x)
       have i₂ := eq2192
       grind)
    | exact superpose eq2192 eq422
    | exact resolve eq422 eq2192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq2201 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq61 (σ x) (σ y) X0
       have i₂ := eq2192
       grind)
    | exact superpose eq2192 eq61
    | exact resolve eq61 eq2192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq2192
  have eq2345 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2201 (σ (M.op y y))
       have i₂ := eq2196
       grind)
    | exact superpose eq2196 eq2201
    | exact resolve eq2201 eq2196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2196 eq2201
  have eq2363 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2345
  have eq2366 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2363
       have i₂ := eq376 y
       grind)
    | exact superpose eq376 eq2363
    | exact resolve eq2363 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376 eq2363
  have eq2378 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq430 y X0
       have i₂ := eq2366
       grind)
    | exact superpose eq2366 eq430
    | (have j0 := eq430 y X0
       grind)
    | (have r₁ := eq430 y x
       have r₂ := eq2366
       grind)
    | exact resolve eq430 eq2366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2366
  have eq2406 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq2378 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2378
  have eq2409 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq2406 X0
       have j1 := eq430 y X0
       grind)
    | (have r₁ := eq2406 X0
       have r₂ := eq430 y x
       grind)
    | exact resolve eq2406 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq2406
  have eq2422 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq2409 (σ X0)
       grind)
    | exact superpose eq2409 eq15
    | exact resolve eq15 eq2409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2409
  have eq2549 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2422 x
       grind)
    | exact superpose eq2422 eq16
    | exact resolve eq16 eq2422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2422
  have eq2649 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2549
       have i₂ := eq1382 x y
       grind)
    | exact superpose eq1382 eq2549
    | (have j1 := eq1382 x y
       grind)
    | (have r₁ := eq2549
       have r₂ := eq1382 x y
       grind)
    | exact resolve eq2549 eq1382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382
  have eq2650 : y = (M.op x y) := by grind
  clear eq2649
  have eq2653 : (σ y) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2194
       have i₂ := eq2650
       grind)
    | exact superpose eq2650 eq2194
    | exact resolve eq2194 eq2650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2194 eq2650
  have eq2671 : y = (M.op y y) := by grind
  clear eq2653
  have eq2676 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq92 y x
       have i₂ := eq2671
       grind)
    | exact superpose eq2671 eq92
    | (have r₁ := eq92 y x
       have r₂ := eq2671
       grind)
    | exact resolve eq92 eq2671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq2671
  have eq2711 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq2676 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2676
  have eq2813 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2549
       have i₂ := eq2711 x
       grind)
    | exact superpose eq2711 eq2549
    | exact resolve eq2549 eq2711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2549 eq2711
  have eq2816 : False := by grind
  exact eq2816

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxy_x_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq61 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq61 X0 X0 X0
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq338 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq339 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq338 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq342 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq339 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq339 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq339 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq357 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq376 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq357 X0
       have i₂ := eq342 X0
       grind)
    | exact superpose eq342 eq357
    | exact resolve eq357 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq357
  have eq422 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0) (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq61
    | exact resolve eq61 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq376 X0
       grind)
    | exact superpose eq376 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq431 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq428 X0 X1
       have j1 := eq430 X0 X1
       grind)
    | (have r₁ := eq428 X0 X1
       have r₂ := eq430 X0 X1
       grind)
    | exact resolve eq428 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq1061 : ∀ X0 X1 : G, (k X1 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq431 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq431
    | exact resolve eq431 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1072 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq431 X1 (σ X0)
       grind)
    | exact superpose eq431 eq15
    | (have j1 := eq431 X1 (σ X0)
       grind)
    | exact resolve eq15 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq1112 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq1061 X1 (τ X0)
       grind)
    | exact superpose eq1061 eq17
    | (have j1 := eq1061 X1 (τ X0)
       grind)
    | exact resolve eq17 eq1061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1061
  have eq1314 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1112 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1112
    | exact resolve eq1112 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1112
  have eq1382 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1314 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1314
    | (have j0 := eq1314 X0 X1
       grind)
    | exact resolve eq1314 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1314
  have eq1888 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1072 x y
       grind)
    | exact superpose eq1072 eq16
    | (have j1 := eq1072 x y
       grind)
    | exact resolve eq16 eq1072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1072
  have eq2098 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1888
       have i₂ := eq1382 x y
       grind)
    | exact superpose eq1382 eq1888
    | (have j1 := eq1382 (σ x) (σ y)
       grind)
    | (have r₁ := eq1888
       have r₂ := eq1382 x y
       grind)
    | exact resolve eq1888 eq1382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888
  have eq2099 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2098
  have eq2105 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61 x y X0
       have i₂ := eq2099
       grind)
    | exact superpose eq2099 eq61
    | exact resolve eq61 eq2099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2099
  have eq2176 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2105 (M.op y x)
       have i₂ := eq2105 x
       grind)
    | exact superpose eq2105 eq2105
    | exact resolve eq2105 eq2105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2105
  have eq2191 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2176
  have eq2193 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2191
       grind)
    | exact superpose eq2191 eq16
    | exact resolve eq16 eq2191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2195 : (σ y) = (M.op (σ y) (σ (M.op y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq422 y (σ x)
       have i₂ := eq2191
       grind)
    | exact superpose eq2191 eq422
    | exact resolve eq422 eq2191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq2200 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq61 (σ x) (σ y) X0
       have i₂ := eq2191
       grind)
    | exact superpose eq2191 eq61
    | exact resolve eq61 eq2191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq2191
  have eq2341 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2200 (σ (M.op y y))
       have i₂ := eq2195
       grind)
    | exact superpose eq2195 eq2200
    | exact resolve eq2200 eq2195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2195 eq2200
  have eq2359 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq2341
  have eq2362 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2359
       have i₂ := eq376 y
       grind)
    | exact superpose eq376 eq2359
    | exact resolve eq2359 eq376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq376 eq2359
  have eq2374 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq430 y X0
       have i₂ := eq2362
       grind)
    | exact superpose eq2362 eq430
    | (have j0 := eq430 y X0
       grind)
    | (have r₁ := eq430 y x
       have r₂ := eq2362
       grind)
    | exact resolve eq430 eq2362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2362
  have eq2402 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    intro X0
    first
    | (have j0 := eq2374 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2374
  have eq2405 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) := by
    intro X0
    first
    | (have j0 := eq2402 X0
       have j1 := eq430 y X0
       grind)
    | (have r₁ := eq2402 X0
       have r₂ := eq430 y x
       grind)
    | exact resolve eq2402 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq2402
  have eq2418 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq2405 (σ X0)
       grind)
    | exact superpose eq2405 eq15
    | exact resolve eq15 eq2405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2405
  have eq2545 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2418 x
       grind)
    | exact superpose eq2418 eq16
    | exact resolve eq16 eq2418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2418
  have eq2644 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2545
       have i₂ := eq1382 x y
       grind)
    | exact superpose eq1382 eq2545
    | (have j1 := eq1382 x y
       grind)
    | (have r₁ := eq2545
       have r₂ := eq1382 x y
       grind)
    | exact resolve eq2545 eq1382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382
  have eq2645 : y = (M.op x y) := by grind
  clear eq2644
  have eq2648 : (σ y) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2193
       have i₂ := eq2645
       grind)
    | exact superpose eq2645 eq2193
    | exact resolve eq2193 eq2645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2193 eq2645
  have eq2666 : y = (M.op y y) := by grind
  clear eq2648
  have eq2671 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq92 y x
       have i₂ := eq2666
       grind)
    | exact superpose eq2666 eq92
    | (have r₁ := eq92 y x
       have r₂ := eq2666
       grind)
    | exact resolve eq92 eq2666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq2666
  have eq2706 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq2671 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2671
  have eq2808 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq2545
       have i₂ := eq2706 x
       grind)
    | exact superpose eq2706 eq2545
    | exact resolve eq2545 eq2706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2545 eq2706
  have eq2811 : False := by grind
  exact eq2811

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pyx_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq19 X0 X0 X0
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
    | (have i₁ := eq32 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq78 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (σ X1) X0) = X0 ∨ (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X1 X0
       have i₂ := eq14 (σ X1) X0
       grind)
    | exact superpose eq14 eq40
    | (have j1 := eq14 X0 X0
       grind)
    | exact resolve eq40 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq79 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) X0) = X0 ∨ (M.op X0 X0) = X0 := by
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
  have eq82 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq32
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq32 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq192 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq77 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq77 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq195 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq194 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq197 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq198 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq197 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq197 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq275 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq195 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq195
    | (have j0 := eq195 (τ X0)
       grind)
    | exact resolve eq195 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq277 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq275 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq275
    | (have j0 := eq275 X0
       grind)
    | exact resolve eq275 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq280 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq277 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq277
    | (have j0 := eq277 X0
       grind)
    | exact resolve eq277 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq286 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq280 (τ X0)
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq280
    | (have j0 := eq280 (τ X0)
       grind)
    | exact resolve eq280 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq280
  have eq405 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
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
  have eq439 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq405 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq405
    | (have j0 := eq405 X0 X1
       grind)
    | exact resolve eq405 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq2972 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq78 (σ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq2973 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 (τ (σ X0))) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq2972 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2972
  have eq2979 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq2973 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2973
    | (have j0 := eq2973 X0
       grind)
    | exact resolve eq2973 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2973
  have eq2983 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2979 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2979
    | exact resolve eq2979 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2979
  have eq3023 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2983 X0
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq2983
    | (have j0 := eq2983 X0
       grind)
    | exact resolve eq2983 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2983
  have eq3028 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (τ (k X0 X0)) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq3023 X0
       grind)
    | exact superpose eq3023 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq3023 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq3023 X0
       grind)
    | exact resolve eq12 eq3023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3023
  have eq3055 : ∀ X0 X1 : G, (τ (k X0 X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq3028 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3028
  have eq3256 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq3055 X0 X1
       grind)
    | exact superpose eq3055 eq11
    | (have j1 := eq3055 X0 X1
       grind)
    | exact resolve eq11 eq3055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3055
  have eq3333 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3256 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq3256
    | (have j0 := eq3256 X0 X0
       grind)
    | exact resolve eq3256 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3256
  have eq3454 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3333 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3333
  have eq3455 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3454 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3454
  have eq3572 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq195 X0
       have i₂ := eq3455 X0
       grind)
    | exact superpose eq3455 eq195
    | (have j0 := eq195 X0
       grind)
    | exact resolve eq195 eq3455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq3573 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq198 X0 X1
       have i₂ := eq3455 X0
       grind)
    | exact superpose eq3455 eq198
    | (have j0 := eq198 X0 X1
       grind)
    | exact resolve eq198 eq3455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq3576 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq286 X0
       have i₂ := eq3455 X0
       grind)
    | exact superpose eq3455 eq286
    | (have j0 := eq286 X0
       grind)
    | exact resolve eq286 eq3455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq3607 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq3455 (σ X0)
       grind)
    | exact superpose eq3455 eq15
    | exact resolve eq15 eq3455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3614 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0 X0
       have i₂ := eq3455 (τ X0)
       grind)
    | exact superpose eq3455 eq43
    | exact resolve eq43 eq3455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq3663 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3614 X0
       have i₂ := eq3455 X0
       grind)
    | exact superpose eq3455 eq3614
    | exact resolve eq3614 eq3455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3614
  have eq3670 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3607 X0
       have i₂ := eq3455 X0
       grind)
    | exact superpose eq3455 eq3607
    | exact resolve eq3607 eq3455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3455 eq3607
  have eq3963 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (σ X0) X1
       have i₂ := eq3670 X0
       grind)
    | exact superpose eq3670 eq34
    | exact resolve eq34 eq3670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3974 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (σ X0) (σ X0)
       have i₂ := eq3670 X0
       grind)
    | exact superpose eq3670 eq19
    | exact resolve eq19 eq3670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5486 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3576 (σ X0)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq3576
    | (have j0 := eq3576 (σ X0)
       have j1 := eq82 X0 X1
       grind)
    | exact resolve eq3576 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq3576
  have eq5497 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq5486 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5486
  have eq5511 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5497 X0 X1
       have i₂ := eq3663 (σ X0)
       grind)
    | exact superpose eq3663 eq5497
    | (have j0 := eq5497 X0 X1
       grind)
    | exact resolve eq5497 eq3663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3663 eq5497
  have eq5527 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5511 X0 X1
       have i₂ := eq3670 X0
       grind)
    | exact superpose eq3670 eq5511
    | (have j0 := eq5511 X0 X1
       grind)
    | exact resolve eq5511 eq3670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5511
  have eq5538 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5527 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq5527
    | (have j0 := eq5527 X0 X1
       grind)
    | exact resolve eq5527 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5527
  have eq5545 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = (M.op X1 (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5538 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5538
    | (have j0 := eq5538 X0 X1
       grind)
    | exact resolve eq5538 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5538
  have eq26432 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) X0)
       have i₂ := eq5545 X1 X0
       grind)
    | exact superpose eq5545 eq11
    | (have j1 := eq5545 X1 X0
       grind)
    | exact resolve eq11 eq5545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5545
  have eq26550 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26432 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq26432
    | (have j0 := eq26432 X0 X1
       grind)
    | exact resolve eq26432 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq26432
  have eq26699 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq26550 (σ X1) X0
       grind)
    | exact superpose eq26550 eq15
    | (have j1 := eq26550 (σ X1) X0
       grind)
    | exact resolve eq15 eq26550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26550
  have eq45594 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq26699 x y
       grind)
    | exact superpose eq26699 eq16
    | (have j1 := eq26699 x y
       grind)
    | exact resolve eq16 eq26699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26699
  have eq46581 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq45594
       have i₂ := eq439 y x
       grind)
    | exact superpose eq439 eq45594
    | (have j1 := eq439 x x
       grind)
    | (have r₁ := eq45594
       have r₂ := eq439 y x
       grind)
    | exact resolve eq45594 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439 eq45594
  have eq46582 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op y x) := by grind
  clear eq46581
  have eq46583 : x = (M.op y x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq46582
  have eq46591 : ∀ X0 : G, x = (M.op x (M.op x X0)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq19 y x X0
       have i₂ := eq46583
       grind)
    | exact superpose eq46583 eq19
    | exact resolve eq19 eq46583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46583
  have eq47158 : x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq46591 (M.op x x)
       have i₂ := eq46591 x
       grind)
    | exact superpose eq46591 eq46591
    | exact resolve eq46591 eq46591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46591
  have eq47202 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq47158
  have eq47675 : (σ x) = (M.op (σ x) (σ (M.op x x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3974 x (σ y)
       have i₂ := eq47202
       grind)
    | exact superpose eq47202 eq3974
    | exact resolve eq3974 eq47202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3974
  have eq47680 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq19 (σ y) (σ x) X0
       have i₂ := eq47202
       grind)
    | exact superpose eq47202 eq19
    | exact resolve eq19 eq47202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq47202
  have eq48853 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq47680 (σ (M.op x x))
       have i₂ := eq47675
       grind)
    | exact superpose eq47675 eq47680
    | exact resolve eq47680 eq47675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47675 eq47680
  have eq48912 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq48853
  have eq48921 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq48912
       have i₂ := eq3670 x
       grind)
    | exact superpose eq3670 eq48912
    | exact resolve eq48912 eq3670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48912
  have eq48937 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq3572 x
       have i₂ := eq48921
       grind)
    | exact superpose eq48921 eq3572
    | (have j0 := eq3572 x
       grind)
    | (have r₁ := eq3572 x
       have r₂ := eq48921
       grind)
    | exact resolve eq3572 eq48921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48953 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq3963 x x
       have i₂ := eq48921
       grind)
    | exact superpose eq48921 eq3963
    | (have r₁ := eq3963 x x
       have r₂ := eq48921
       grind)
    | exact resolve eq3963 eq48921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3963 eq48921
  have eq49012 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have j0 := eq48953 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48953
  have eq49019 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq48937
  have eq49028 : ∀ X0 : G, (k X0 (σ x)) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have j0 := eq49012 X0
       have j1 := eq3573 x X0
       grind)
    | (have r₁ := eq49012 X0
       have r₂ := eq3573 x x
       grind)
    | exact resolve eq49012 eq3573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3573 eq49012
  have eq49035 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq3572 x
       grind)
    | (have r₁ := eq49019
       have r₂ := eq3572 x
       grind)
    | exact resolve eq49019 eq3572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3572 eq49019
  have eq49044 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq49035
       have i₂ := eq3670 x
       grind)
    | exact superpose eq3670 eq49035
    | exact resolve eq49035 eq3670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3670 eq49035
  have eq50031 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq49044
       grind)
    | exact superpose eq49044 eq10
    | exact resolve eq10 eq49044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49044
  have eq50266 : x = (M.op x x) := by
    first
    | (have i₁ := eq50031
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq50031
    | exact resolve eq50031 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50031
  have eq50335 : ∀ X0 : G, x ≠ x ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq34 x x
       have i₂ := eq50266
       grind)
    | exact superpose eq50266 eq34
    | (have r₁ := eq34 x x
       have r₂ := eq50266
       grind)
    | exact resolve eq34 eq50266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq50266
  have eq50431 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq50335 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50335
  have eq51284 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq49028 (σ X0)
       grind)
    | exact superpose eq49028 eq15
    | exact resolve eq15 eq49028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49028
  have eq51399 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq51284 X0
       have i₂ := eq50431 X0
       grind)
    | exact superpose eq50431 eq51284
    | exact resolve eq51284 eq50431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50431 eq51284
  have eq53521 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq51399 y
       grind)
    | exact superpose eq51399 eq16
    | (have r₁ := eq16
       have r₂ := eq51399 y
       grind)
    | exact resolve eq16 eq51399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51399
  have eq53665 : False := by grind
  exact eq53665

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pxy_pyy_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
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
  have eq45 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq35
    | (have j0 := eq35 (M.op x y)
       grind)
    | exact resolve eq35 eq20
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
  have eq52 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq14 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq14 (M.op X0 X3) (M.op x x) X0 X4
       have i₂ := eq14 X0 x x X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq76 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq76
    | (have j0 := eq76 (σ X0) (σ X1)
       grind)
    | exact resolve eq76 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq76 x y
       grind)
    | exact superpose eq76 eq44
    | (have j1 := eq76 x y
       grind)
    | exact resolve eq44 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100
    | exact resolve eq100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq110 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq20 eq108
    | exact resolve eq108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq128 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq243 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq52 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 x y X0
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq52
    | (have j0 := eq52 X0 x y
       grind)
    | exact resolve eq52 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 (σ x) (σ y)
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq626 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (σ X1) X2)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (σ X0) (σ X1) X2
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq52
    | (have j1 := eq92 X0 X1
       grind)
    | exact resolve eq52 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq627 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (M.op (σ (k X0 X1)) X2)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (σ X0) (σ X1) x
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq53
    | (have j1 := eq92 X0 X1
       grind)
    | exact resolve eq53 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq92
  have eq710 : ∀ X0 : G, (k (τ X0) x) = (τ (k X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq347 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq347
    | (have j0 := eq347 X0 x
       grind)
    | exact resolve eq347 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq901 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq110 eq76
    | (have j0 := eq76 (σ x) (σ y)
       grind)
    | exact resolve eq76 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq902 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq26 eq901
    | exact resolve eq901 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901
  have eq905 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq902
       have r₂ := eq27
       grind)
    | exact resolve eq902 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq908 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq905 eq253
    | exact resolve eq253 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq915 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq905 eq52
    | exact resolve eq52 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1076 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq908 eq915
    | exact resolve eq915 eq908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq908 eq915
  have eq1092 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y x) := by grind
  clear eq1076
  have eq1121 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq1092 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1092
       grind)
    | exact resolve eq13 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1135 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq1121 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1121
  have eq1317 : (k x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1135 eq49
    | exact resolve eq49 eq1135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq1135
  have eq1332 : (τ (σ x)) = (k x x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1092 eq1317
    | exact resolve eq1317 eq1092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092 eq1317
  have eq1342 : (τ (σ x)) = (k x x) ∨ x = (M.op y x) := by grind
  clear eq1332
  have eq1344 : x = (k x x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq1342
    | exact resolve eq1342 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342
  have eq1347 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq76 x x
       have i₂ := eq1344
       grind)
    | exact superpose eq1344 eq76
    | (have j0 := eq76 x x
       grind)
    | exact resolve eq76 eq1344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344
  have eq1348 : x = (M.op y x) ∨ x = (M.op x x) := by grind
  clear eq1347
  have eq1352 : x = (M.op x (M.op x y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq252 y
       have i₂ := eq1348
       grind)
    | exact superpose eq1348 eq252
    | exact resolve eq252 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1359 : ∀ X0 : G, x = (M.op x (M.op x X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq52 y x X0
       have i₂ := eq1348
       grind)
    | exact superpose eq1348 eq52
    | exact resolve eq52 eq1348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq1348
  have eq1498 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1352 eq1359
    | exact resolve eq1359 eq1352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352 eq1359
  have eq1516 : x = (M.op x x) := by grind
  clear eq1498
  have eq1518 : x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq252 x
       have i₂ := eq1516
       grind)
    | exact superpose eq1516 eq252
    | exact resolve eq252 eq1516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq1519 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq1516
       grind)
    | exact superpose eq1516 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq1516
       grind)
    | exact resolve eq13 eq1516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1534 : ∀ X0 : G, (k X0 x) = (M.op X0 x) := by
    intro X0
    first
    | (have j0 := eq1519 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1519
  have eq1666 : ∀ X0 : G, (τ (k X0 (σ x))) = (M.op (τ X0) x) := by
    intro X0
    first
    | (have i₁ := eq1534 (τ X0)
       have i₂ := eq710 X0
       grind)
    | exact superpose eq710 eq1534
    | exact resolve eq1534 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq1670 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq1534 x
       grind)
    | exact superpose eq1534 eq43
    | exact resolve eq43 eq1534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1671 : (k (σ y) (σ x)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq1534 y
       grind)
    | exact superpose eq1534 eq73
    | exact resolve eq73 eq1534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq1672 : (k (σ (M.op x y)) (σ x)) = (σ (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq128
       have i₂ := eq1534 sF0
       grind)
    | exact superpose eq1534 eq128
    | exact resolve eq128 eq1534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128 eq1534
  have eq1676 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1670
       have i₂ := eq1516
       grind)
    | exact superpose eq1516 eq1670
    | exact resolve eq1670 eq1516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670
  have eq1677 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1676
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1676
    | exact resolve eq1676 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1676
  have eq1682 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1677 eq76
    | (have j0 := eq76 (σ x) (σ x)
       grind)
    | exact resolve eq76 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677
  have eq1683 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1682
  have eq1692 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq1683 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq1683
       grind)
    | exact resolve eq13 eq1683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1707 : ∀ X0 : G, (k X0 (σ x)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq1692 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692
  have eq2652 : (σ (M.op y x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1707 eq1671
    | exact resolve eq1671 eq1707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1671
  have eq2722 : (M.op (σ (M.op x y)) (σ x)) = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq1707 eq1672
    | exact resolve eq1672 eq1707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672
  have eq2727 : (M.op y x) = (τ (M.op (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op y x)
       have i₂ := eq2652
       grind)
    | exact superpose eq2652 eq16
    | exact resolve eq16 eq2652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2652
  have eq2826 : (τ (σ x)) = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq905 eq2727
    | exact resolve eq2727 eq905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905 eq2727
  have eq2850 : x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | exact superpose eq28 eq2826
    | exact resolve eq2826 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2826
  have eq2851 : x = (M.op y x) := by grind
  clear eq2850
  have eq2856 : y = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq243 x
       have i₂ := eq2851
       grind)
    | exact superpose eq2851 eq243
    | exact resolve eq243 eq2851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243 eq2851
  have eq2879 : (σ y) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq2856 eq2722
    | exact resolve eq2722 eq2856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2904 : (σ y) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq2879
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2879
    | exact resolve eq2879 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2879
  have eq3956 : ∀ X0 : G, (M.op (τ X0) x) = (τ (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq1707 eq1666
    | exact resolve eq1666 eq1707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1666 eq1707
  have eq4014 : ∀ X0 : G, (M.op X0 x) = (τ (M.op (σ X0) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq3956 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq3956
    | exact resolve eq3956 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4022 : (τ (M.op (k (σ x) (σ (M.op x y))) (σ x))) = (M.op (k x (M.op x y)) x) := by
    first
    | exact superpose eq64 eq3956
    | exact resolve eq3956 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq3956
  have eq4236 : ∀ X0 : G, (M.op (σ X0) (σ x)) = (σ (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq4014 eq15
    | exact resolve eq15 eq4014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4014
  have eq6732 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ x) (σ (M.op x y))) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq45 eq626
    | (have j0 := eq626 x (M.op x y) x
       grind)
    | exact resolve eq626 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq6827 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ x) (σ (M.op x y))) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq20 eq6732
    | (have j0 := eq6732 X0
       grind)
    | exact resolve eq6732 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6732
  have eq6869 : ∀ X0 : G, (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (k (σ x) (σ (M.op x y))) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq6827 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6827
    | (have j0 := eq6827 X0
       grind)
    | exact resolve eq6827 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6827
  have eq6899 : ∀ X0 : G, (σ x) = (σ (M.op (M.op x y) x)) ∨ (σ (M.op x y)) = (M.op (k (σ x) (σ (M.op x y))) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq4236 eq6869
    | (have j0 := eq6869 X0
       grind)
    | exact resolve eq6869 eq4236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6869
  have eq6916 : ∀ X0 : G, (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (k (σ x) (σ (M.op x y))) (M.op (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq2722 eq6899
    | (have j0 := eq6899 X0
       grind)
    | exact resolve eq6899 eq2722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6899
  have eq6927 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ x) (σ (M.op x y))) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq2904 eq6916
    | (have j0 := eq6916 X0
       grind)
    | exact resolve eq6916 eq2904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6916
  have eq7004 : ∀ X0 : G, (k (σ x) (σ (M.op x y))) = (M.op (σ x) (M.op (k (σ x) (σ (M.op x y))) X0)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq45 eq627
    | (have j0 := eq627 x (M.op x y) x
       grind)
    | exact resolve eq627 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq627
  have eq7052 : ∀ X0 : G, (k (σ x) (σ (M.op x y))) = (M.op (σ x) (M.op (k (σ x) (σ (M.op x y))) X0)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq7004 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7004
    | (have j0 := eq7004 X0
       grind)
    | exact resolve eq7004 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7004
  have eq7094 : ∀ X0 : G, (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (M.op (k (σ x) (σ (M.op x y))) X0)) := by
    intro X0
    first
    | (have i₁ := eq7052 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7052
    | (have j0 := eq7052 X0
       grind)
    | exact resolve eq7052 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7052
  have eq7129 : ∀ X0 : G, (σ x) = (σ (M.op (M.op x y) x)) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (M.op (k (σ x) (σ (M.op x y))) X0)) := by
    intro X0
    first
    | exact superpose eq4236 eq7094
    | (have j0 := eq7094 X0
       grind)
    | exact resolve eq7094 eq4236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4236 eq7094
  have eq7149 : ∀ X0 : G, (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (k (σ x) (σ (M.op x y))) = (M.op (σ x) (M.op (k (σ x) (σ (M.op x y))) X0)) := by
    intro X0
    first
    | exact superpose eq2722 eq7129
    | (have j0 := eq7129 X0
       grind)
    | exact resolve eq7129 eq2722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2722 eq7129
  have eq7162 : ∀ X0 : G, (k (σ x) (σ (M.op x y))) = (M.op (σ x) (M.op (k (σ x) (σ (M.op x y))) X0)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq2904 eq7149
    | (have j0 := eq7149 X0
       grind)
    | exact resolve eq7149 eq2904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7149
  have eq9593 : (σ (M.op x y)) = (M.op (k (σ x) (σ (M.op x y))) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2904 eq6927
    | exact resolve eq6927 eq2904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2904 eq6927
  have eq10474 : (M.op (k (σ x) (σ (M.op x y))) (σ x)) = (σ (M.op (k x (M.op x y)) x)) := by
    first
    | exact superpose eq4022 eq15
    | exact resolve eq15 eq4022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4022
  have eq11797 : (M.op (k (σ x) (σ (M.op x y))) (σ x)) = (σ (M.op (M.op x (M.op x y)) x)) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq10474
       have i₂ := eq76 x sF0
       grind)
    | exact superpose eq76 eq10474
    | (have j1 := eq76 x (M.op x y)
       grind)
    | exact resolve eq10474 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq10474
  have eq11852 : (σ (M.op x x)) = (M.op (k (σ x) (σ (M.op x y))) (σ x)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq1518 eq11797
    | exact resolve eq11797 eq1518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518 eq11797
  have eq11857 : (σ x) = (M.op (k (σ x) (σ (M.op x y))) (σ x)) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq11852
       have i₂ := eq1516
       grind)
    | exact superpose eq1516 eq11852
    | exact resolve eq11852 eq1516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11852
  have eq11859 : (σ x) = (M.op (k (σ x) (σ (M.op x y))) (σ x)) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq11857
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11857
    | exact resolve eq11857 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11857
  have eq11861 : (σ x) = (M.op (k (σ x) (σ (M.op x y))) (σ x)) ∨ x = y := by
    first
    | exact superpose eq2856 eq11859
    | exact resolve eq11859 eq2856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2856 eq11859
  have eq11865 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11861 eq7162
    | exact resolve eq7162 eq11861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7162 eq11861
  have eq11903 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1683 eq11865
    | exact resolve eq11865 eq1683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11865
  have eq11956 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq11903 eq9593
    | exact resolve eq9593 eq11903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9593 eq11903
  have eq11969 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq11956
  have eq11982 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq11969
    | exact resolve eq11969 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11969
  have eq11989 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq11982
       have r₂ := eq27
       grind)
    | exact resolve eq11982 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11982
  have eq11992 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq11989 eq29
    | exact resolve eq29 eq11989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq11989
  have eq12064 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq11992
    | exact resolve eq11992 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq11992
  have eq12065 : x = y := by grind
  clear eq12064
  have eq12133 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq12065
       grind)
    | exact superpose eq12065 eq18
    | exact resolve eq18 eq12065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq12134 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq12065
       grind)
    | exact superpose eq12065 eq24
    | exact resolve eq24 eq12065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq12065
  have eq12199 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq12134
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12134
    | exact resolve eq12134 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12134
  have eq12200 : x = (M.op x y) := by
    first
    | (have i₁ := eq12133
       have i₂ := eq1516
       grind)
    | exact superpose eq1516 eq12133
    | exact resolve eq12133 eq1516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516 eq12133
  have eq12216 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq12199 eq26
    | exact resolve eq26 eq12199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq12199
  have eq12296 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1683 eq12216
    | exact resolve eq12216 eq1683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1683 eq12216
  have eq12318 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq12200 eq20
    | exact resolve eq20 eq12200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq12200
  have eq12413 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq12318
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq12318
    | exact resolve eq12318 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq12318
  have eq12534 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq12296 eq27
    | exact resolve eq27 eq12296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq12296
  have eq12919 : False := by grind
  exact eq12919

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_pxx_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq19 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
    intro X0 X4 X5
    first
    | (have i₁ := eq9 X4 (M.op (M.op x x) X0) (M.op X0 x) X5
       have i₂ := eq9 X0 x x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq19 X0 X0 X0
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
    | (have i₁ := eq32 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq32
    | exact resolve eq32 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq79 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (M.op X0 X0) = X0 := by
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
  have eq82 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X1 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq32
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq32 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq183 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq77 X1 X0
       grind)
    | exact superpose eq77 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq77 X1 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq13 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (M.op X2 (σ X1)) (σ (k X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 X2 (σ X1) (σ X0)
       have i₂ := eq77 X1 X0
       grind)
    | exact superpose eq77 eq19
    | (have j1 := eq77 X1 X1
       grind)
    | exact resolve eq19 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (σ X1) (σ X0) X2
       have i₂ := eq77 X1 X0
       grind)
    | exact superpose eq77 eq19
    | (have j1 := eq77 X1 X1
       grind)
    | exact resolve eq19 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq77 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq77 X1 X1
       grind)
    | (have r₁ := eq12 X0 (σ X0)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq77 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq195 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq194 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq196 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq192 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq197 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq183 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq198 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq196 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq196 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq199 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 X1
       have j1 := eq13 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq197 X0 X1
       have r₂ := eq13 (σ X1) (σ X1)
       grind)
    | (have r₁ := eq197 X0 X1
       have r₂ := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq197 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq202 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq199 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq199
    | (have j0 := eq199 X0 X1
       grind)
    | exact resolve eq199 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq276 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq195 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq195
    | (have j0 := eq195 (τ X0)
       grind)
    | exact resolve eq195 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq278 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq276 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq276
    | (have j0 := eq276 X0
       grind)
    | exact resolve eq276 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq281 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq278 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq278
    | (have j0 := eq278 X0
       grind)
    | exact resolve eq278 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq287 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq281 (τ X0)
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq281
    | (have j0 := eq281 (τ X0)
       grind)
    | exact resolve eq281 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq406 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
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
  have eq440 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq406 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq406
    | (have j0 := eq406 X0 X1
       grind)
    | exact resolve eq406 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq806 : ∀ X0 X1 : G, (σ (σ X0)) ≠ (σ (σ (k X0 X1))) ∨ (M.op (σ (σ X0)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (σ X1)) = (M.op (σ (σ X1)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq202 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq202
    | (have j0 := eq202 X0 (σ X1)
       grind)
    | exact resolve eq202 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq944 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq945 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq944 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq1160 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq185 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq1161 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (k X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1160 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq2253 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X1 X0) (σ (k (τ X0) (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq945 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq945
    | exact resolve eq945 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq2291 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k (σ (τ X0)) X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2253 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2253
    | (have j0 := eq2253 X0 X1
       grind)
    | exact resolve eq2253 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2253
  have eq2292 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2291 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2291
    | (have j0 := eq2291 X0 X1
       grind)
    | exact resolve eq2291 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2291
  have eq2368 : ∀ X0 X2 : G, (k X0 X0) = (M.op X0 (M.op (k X0 X0) X2)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq19 (M.op x X0) (k X0 X0) X2
       have i₂ := eq2292 X0 x
       grind)
    | exact superpose eq2292 eq19
    | (have j1 := eq2292 X0 x
       grind)
    | exact resolve eq19 eq2292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2292
  have eq2415 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (σ (k (τ X0) (τ X0))) (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1161 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1161
    | exact resolve eq1161 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161
  have eq2453 : ∀ X0 X1 : G, (M.op (k (σ (τ X0)) X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2415 X0 X1
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq2415
    | (have j0 := eq2415 X0 X1
       grind)
    | exact resolve eq2415 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2415
  have eq2454 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op X0 X1)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2453 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2453
    | (have j0 := eq2453 X0 X1
       grind)
    | exact resolve eq2453 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2453
  have eq2468 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2368 X0 (M.op X0 x)
       have i₂ := eq2454 X0 x
       grind)
    | exact superpose eq2454 eq2368
    | (have j0 := eq2368 X0 x
       have j1 := eq2454 X0 x
       grind)
    | exact resolve eq2368 eq2454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2368 eq2454
  have eq2483 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq2468 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2468
  have eq2487 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2483 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq2483 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq2483 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2483
  have eq2493 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq198 X0 X1
       have i₂ := eq2487 X0
       grind)
    | exact superpose eq2487 eq198
    | (have j0 := eq198 X0 X1
       grind)
    | exact resolve eq198 eq2487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq2496 : ∀ X0 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq287 X0
       have i₂ := eq2487 X0
       grind)
    | exact superpose eq2487 eq287
    | (have j0 := eq287 X0
       grind)
    | exact resolve eq287 eq2487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287
  have eq2505 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq193 X0 X0
       have i₂ := eq2487 X0
       grind)
    | exact superpose eq2487 eq193
    | (have j0 := eq193 X0 X0
       grind)
    | exact resolve eq193 eq2487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq2527 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2487 (σ X0)
       grind)
    | exact superpose eq2487 eq15
    | exact resolve eq15 eq2487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2535 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0 X0
       have i₂ := eq2487 (τ X0)
       grind)
    | exact superpose eq2487 eq43
    | exact resolve eq43 eq2487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2557 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq2505 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2505
  have eq2578 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2535 X0
       have i₂ := eq2487 X0
       grind)
    | exact superpose eq2487 eq2535
    | exact resolve eq2535 eq2487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2535
  have eq2585 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2527 X0
       have i₂ := eq2487 X0
       grind)
    | exact superpose eq2487 eq2527
    | exact resolve eq2527 eq2487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2527
  have eq2824 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (σ X0) (σ X0)
       have i₂ := eq2585 X0
       grind)
    | exact superpose eq2585 eq19
    | exact resolve eq19 eq2585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2825 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (σ X0) (σ X0) X1
       have i₂ := eq2585 X0
       grind)
    | exact superpose eq2585 eq19
    | exact resolve eq19 eq2585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4071 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2496 (σ X0)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq2496
    | (have j0 := eq2496 (σ X0)
       have j1 := eq82 X0 X1
       grind)
    | exact resolve eq2496 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq2496
  have eq4094 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4071 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4071
  have eq4104 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4094 X0 X1
       have i₂ := eq2578 (σ X0)
       grind)
    | exact superpose eq2578 eq4094
    | (have j0 := eq4094 X0 X1
       grind)
    | exact resolve eq4094 eq2578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4094
  have eq4109 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X0 X0))) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4104 X0 X1
       have i₂ := eq2585 X0
       grind)
    | exact superpose eq2585 eq4104
    | (have j0 := eq4104 X0 X1
       grind)
    | exact resolve eq4104 eq2585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4104
  have eq4111 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (M.op (σ X0) X1) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4109 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq4109
    | (have j0 := eq4109 X0 X1
       grind)
    | exact resolve eq4109 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4109
  have eq4113 : ∀ X0 X1 : G, (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (M.op (σ X0) X1) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4111 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4111
    | (have j0 := eq4111 X0 X1
       grind)
    | exact resolve eq4111 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4111
  have eq15131 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X1) X0)
       have i₂ := eq4113 X1 X0
       grind)
    | exact superpose eq4113 eq11
    | (have j1 := eq4113 X1 X0
       grind)
    | exact resolve eq11 eq4113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4113
  have eq15224 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15131 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq15131
    | (have j0 := eq15131 X0 X1
       grind)
    | exact resolve eq15131 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq15131
  have eq15293 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15224 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15224
    | (have j0 := eq15224 X0 (τ X0)
       grind)
    | exact resolve eq15224 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15358 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq15224 (σ X1) X0
       grind)
    | exact superpose eq15224 eq15
    | (have j1 := eq15224 (σ X1) X0
       grind)
    | exact resolve eq15 eq15224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15224
  have eq15427 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15293 X0 X1
       have i₂ := eq2578 X0
       grind)
    | exact superpose eq2578 eq15293
    | (have j0 := eq15293 X0 X1
       grind)
    | exact resolve eq15293 eq2578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15293
  have eq15943 : ∀ X0 X1 X2 : G, (k (τ X0) (τ X1)) = (τ (k (M.op X0 X0) X1)) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 X1 (M.op X0 X0)
       have i₂ := eq15427 X0 X2
       grind)
    | exact superpose eq15427 eq43
    | (have j1 := eq15427 X0 X2
       grind)
    | exact resolve eq43 eq15427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15427
  have eq16101 : ∀ X0 X1 X2 : G, (τ (k X0 X1)) = (τ (k (M.op X0 X0) X1)) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15943 X0 X1 X2
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq15943
    | (have j0 := eq15943 X0 X1 X2
       grind)
    | exact resolve eq15943 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15943
  have eq24652 : ∀ X0 X1 : G, (σ (σ (τ X0))) ≠ (σ (σ (τ (k X0 X1)))) ∨ (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) = (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq806 (τ X1) (τ X0)
       have i₂ := eq43 X0 X1
       grind)
    | exact superpose eq43 eq806
    | (have j0 := eq806 X0 (τ X1)
       grind)
    | exact resolve eq806 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq24735 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (σ (τ X0))) ∨ (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) = (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq24652 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq24652
    | (have j0 := eq24652 X0 X1
       grind)
    | exact resolve eq24652 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24652
  have eq24794 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) = (σ (σ (τ (k X0 X1)))) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq24735 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24735
    | (have j0 := eq24735 X0 X1
       grind)
    | exact resolve eq24735 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24735
  have eq24853 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ (σ (τ X0))) (σ (σ (τ X0)))) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq24794 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq24794
    | (have j0 := eq24794 X0 X1
       grind)
    | exact resolve eq24794 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24794
  have eq24912 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op (σ (τ X0)) (σ (τ X0)))) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq24853 X0 X1
       have i₂ := eq2585 (σ (τ X0))
       grind)
    | exact superpose eq2585 eq24853
    | (have j0 := eq24853 X0 X1
       grind)
    | exact resolve eq24853 eq2585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24853
  have eq24969 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (σ (M.op (τ X0) (τ X0)))) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq24912 X0 X1
       have i₂ := eq2585 (τ X0)
       grind)
    | exact superpose eq2585 eq24912
    | (have j0 := eq24912 X0 X1
       grind)
    | exact resolve eq24912 eq2585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24912
  have eq25022 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (σ (τ (M.op X0 X0)))) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq24969 X0 X1
       have i₂ := eq2578 X0
       grind)
    | exact superpose eq2578 eq24969
    | (have j0 := eq24969 X0 X1
       grind)
    | exact resolve eq24969 eq2578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24969
  have eq25055 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (σ (τ X1))) = (M.op (σ (σ (τ X1))) (σ (σ (τ X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq25022 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq25022
    | (have j0 := eq25022 X0 X1
       grind)
    | exact resolve eq25022 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25022
  have eq25083 : ∀ X0 X1 : G, (σ (σ (τ X1))) = (σ (M.op (σ (τ X1)) (σ (τ X1)))) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25055 X0 X1
       have i₂ := eq2585 (σ (τ X1))
       grind)
    | exact superpose eq2585 eq25055
    | (have j0 := eq25055 X0 X1
       grind)
    | exact resolve eq25055 eq2585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25055
  have eq25098 : ∀ X0 X1 : G, (σ (σ (τ X1))) = (σ (σ (M.op (τ X1) (τ X1)))) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25083 X0 X1
       have i₂ := eq2585 (τ X1)
       grind)
    | exact superpose eq2585 eq25083
    | (have j0 := eq25083 X0 X1
       grind)
    | exact resolve eq25083 eq2585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25083
  have eq25109 : ∀ X0 X1 : G, (σ (σ (τ X1))) = (σ (σ (τ (M.op X1 X1)))) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25098 X0 X1
       have i₂ := eq2578 X1
       grind)
    | exact superpose eq2578 eq25098
    | (have j0 := eq25098 X0 X1
       grind)
    | exact resolve eq25098 eq2578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2578 eq25098
  have eq25120 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (τ X1))) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) ≠ (σ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25109 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq25109
    | (have j0 := eq25109 X0 X1
       grind)
    | exact resolve eq25109 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25109
  have eq25130 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq25120 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq25120
    | (have j0 := eq25120 X0 X1
       grind)
    | exact resolve eq25120 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25120
  have eq33162 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15358 x y
       grind)
    | exact superpose eq15358 eq16
    | (have j1 := eq15358 x y
       grind)
    | exact resolve eq16 eq15358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33290 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq15358 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15358
  have eq34364 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq33162
       have i₂ := eq440 y x
       grind)
    | exact superpose eq440 eq33162
    | (have j1 := eq440 x x
       grind)
    | (have r₁ := eq33162
       have r₂ := eq440 y x
       grind)
    | exact resolve eq33162 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440 eq33162
  have eq34365 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq34364
  have eq34366 : y = (M.op x y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq34365
  have eq34371 : y ≠ y ∨ (k y x) = (M.op y y) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq34366
       grind)
    | exact superpose eq34366 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq34366
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq34366
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq34366
       grind)
    | exact resolve eq13 eq34366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34366
  have eq34396 : y ≠ y ∨ (k y x) = (M.op y y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq34371
  have eq34397 : (k y x) = (M.op y y) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq34396
  have eq35399 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33290 x y
       have i₂ := eq34397
       grind)
    | exact superpose eq34397 eq33290
    | (have j0 := eq33290 x y
       grind)
    | exact resolve eq33290 eq34397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33290 eq34397
  have eq35401 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq35399
  have eq44837 : ∀ X0 X1 X2 : G, (σ (τ (k X0 X1))) = (k (M.op X0 X0) X1) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k (M.op X0 X0) X1)
       have i₂ := eq16101 X0 X1 X2
       grind)
    | exact superpose eq16101 eq11
    | (have j1 := eq16101 X0 X1 X2
       grind)
    | exact resolve eq11 eq16101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16101
  have eq45053 : ∀ X0 X1 X2 : G, (k X0 X1) = (k (M.op X0 X0) X1) ∨ (M.op X0 X2) = (k X2 X0) ∨ (M.op X0 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq44837 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq44837
    | (have j0 := eq44837 X0 X1 X2
       grind)
    | exact resolve eq44837 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44837
  have eq45147 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2487 (M.op X0 X0)
       have i₂ := eq45053 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq45053 eq2487
    | (have j1 := eq45053 X0 X1 X1
       grind)
    | exact resolve eq2487 eq45053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2487 eq45053
  have eq45308 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45147 X0 X1
       have i₂ := eq19 X0 X0 X0
       grind)
    | (have i₁ := eq45147 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq19 eq45147
    | (have j0 := eq45147 X0 X1
       grind)
    | exact resolve eq45147 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45147
  have eq45952 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq45308 (σ X0) X1
       grind)
    | exact superpose eq45308 eq40
    | (have j1 := eq45308 (σ X0) X1
       grind)
    | exact resolve eq40 eq45308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq45308
  have eq46094 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ (M.op X0 X0)))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45952 X0 X1
       have i₂ := eq2585 X0
       grind)
    | exact superpose eq2585 eq45952
    | (have j0 := eq45952 X0 X1
       grind)
    | exact resolve eq45952 eq2585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45952
  have eq46208 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46094 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq46094
    | (have j0 := eq46094 X0 X1
       grind)
    | exact resolve eq46094 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46094
  have eq46251 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = X0 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46208 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq46208
    | (have j0 := eq46208 X0 X1
       grind)
    | exact resolve eq46208 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46208
  have eq50927 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq25130 X0 (M.op X0 X0)
       have i₂ := eq46251 X0 X1
       grind)
    | exact superpose eq46251 eq25130
    | (have j0 := eq25130 X0 X0
       have j1 := eq46251 X0 X1
       grind)
    | exact resolve eq25130 eq46251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25130 eq46251
  have eq51011 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq50927 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50927
  have eq51075 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq51011 X0 X1
       have j1 := eq2493 X0 X1
       grind)
    | (have r₁ := eq51011 X0 X1
       have r₂ := eq2493 X0 X1
       grind)
    | (have r₁ := eq51011 X0 X1
       have r₂ := eq2493 (M.op X0 X0) X1
       grind)
    | exact resolve eq51011 eq2493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51011
  have eq51146 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51075 X0 X1
       have i₂ := eq19 X0 X0 X0
       grind)
    | (have i₁ := eq51075 X0 X1
       have i₂ := eq19 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq19 eq51075
    | (have j0 := eq51075 X0 X1
       grind)
    | exact resolve eq51075 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51075
  have eq51207 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq51146 X0 X1
       have j1 := eq2493 X0 X1
       grind)
    | (have r₁ := eq51146 X0 X1
       have r₂ := eq2493 X0 X1
       grind)
    | exact resolve eq51146 eq2493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2493 eq51146
  have eq51262 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq51207 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq51207
    | exact resolve eq51207 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51364 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq51207 X0 (σ X1)
       grind)
    | exact superpose eq51207 eq15
    | (have j1 := eq51207 X0 (σ X1)
       grind)
    | exact resolve eq15 eq51207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51207
  have eq52144 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq51262 (τ X0) X1
       grind)
    | exact superpose eq51262 eq18
    | (have j1 := eq51262 (τ X0) X1
       grind)
    | exact resolve eq18 eq51262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq51262
  have eq53465 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52144 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq52144
    | exact resolve eq52144 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52144
  have eq53756 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53465 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq53465
    | (have j0 := eq53465 X0 X1
       grind)
    | exact resolve eq53465 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53465
  have eq56072 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq51364 x y
       grind)
    | exact superpose eq51364 eq16
    | (have j1 := eq51364 x y
       grind)
    | exact resolve eq16 eq51364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56220 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq51364 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51364
  have eq56614 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq56220 (τ X1) (τ X0)
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq56220
    | (have j0 := eq56220 (τ X1) (τ X0)
       grind)
    | exact resolve eq56220 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq56220
  have eq56701 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq56614 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq56614
    | (have j0 := eq56614 X0 X1
       grind)
    | exact resolve eq56614 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56614
  have eq56731 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq56701 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56701
    | (have j0 := eq56701 X0 X1
       grind)
    | exact resolve eq56701 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56701
  have eq56750 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq56731 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56731
    | (have j0 := eq56731 X0 X1
       grind)
    | exact resolve eq56731 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56731
  have eq56763 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq56750 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq56750
    | (have j0 := eq56750 X0 X1
       grind)
    | exact resolve eq56750 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56750
  have eq57620 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq56072
       have i₂ := eq53756 x y
       grind)
    | exact superpose eq53756 eq56072
    | (have j1 := eq53756 (σ x) (σ y)
       grind)
    | (have r₁ := eq56072
       have r₂ := eq53756 x y
       grind)
    | exact resolve eq56072 eq53756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53756
  have eq57623 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq57620
  have eq57802 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19 x y X0
       have i₂ := eq57623
       grind)
    | exact superpose eq57623 eq19
    | exact resolve eq19 eq57623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57623
  have eq58040 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq57802 (M.op y x)
       have i₂ := eq57802 x
       grind)
    | exact superpose eq57802 eq57802
    | exact resolve eq57802 eq57802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57802
  have eq58090 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq58040
  have eq58122 : (σ y) = (M.op (σ y) (σ (M.op y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq2824 y (σ x)
       have i₂ := eq58090
       grind)
    | exact superpose eq58090 eq2824
    | exact resolve eq2824 eq58090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824
  have eq58127 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq19 (σ x) (σ y) X0
       have i₂ := eq58090
       grind)
    | exact superpose eq58090 eq19
    | exact resolve eq19 eq58090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq58090
  have eq60187 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq58127 (σ (M.op y y))
       have i₂ := eq58122
       grind)
    | exact superpose eq58122 eq58127
    | exact resolve eq58127 eq58122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58122 eq58127
  have eq60267 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq60187
  have eq60289 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq60267
       have i₂ := eq2585 y
       grind)
    | exact superpose eq2585 eq60267
    | exact resolve eq60267 eq2585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60267
  have eq60301 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq35401
       have i₂ := eq60289
       grind)
    | exact superpose eq60289 eq35401
    | (have r₁ := eq35401
       have r₂ := eq60289
       grind)
    | exact resolve eq35401 eq60289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60316 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq2557 y
       have i₂ := eq60289
       grind)
    | exact superpose eq60289 eq2557
    | (have j0 := eq2557 y
       grind)
    | (have r₁ := eq2557 y
       have r₂ := eq60289
       grind)
    | exact resolve eq2557 eq60289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60289
  have eq60385 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq60316
  have eq60393 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq60301
  have eq60395 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq2557 y
       grind)
    | (have r₁ := eq60385
       have r₂ := eq2557 y
       grind)
    | exact resolve eq60385 eq2557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60385
  have eq60400 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq60393
       have r₂ := eq35401
       grind)
    | exact resolve eq60393 eq35401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35401 eq60393
  have eq60401 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq60395
       have i₂ := eq2585 y
       grind)
    | exact superpose eq2585 eq60395
    | exact resolve eq60395 eq2585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60395
  have eq79976 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq60400
       grind)
    | exact superpose eq60400 eq16
    | exact resolve eq16 eq60400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80009 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq60400
       grind)
    | exact superpose eq60400 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq60400
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq60400
       grind)
    | exact resolve eq13 eq60400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60400
  have eq80039 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq80009
  have eq80048 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq80039
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq80039
    | exact resolve eq80039 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80039
  have eq80065 : (σ (k y x)) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq80048
       have i₂ := eq2585 y
       grind)
    | exact superpose eq2585 eq80048
    | exact resolve eq80048 eq2585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80048
  have eq80067 : (σ y) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq80065
       have i₂ := eq60401
       grind)
    | exact superpose eq60401 eq80065
    | exact resolve eq80065 eq60401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60401 eq80065
  have eq80068 : x = (M.op x x) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq80067
       have i₂ := eq2585 x
       grind)
    | exact superpose eq2585 eq80067
    | exact resolve eq80067 eq2585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80067
  have eq684242 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2557 x
       have i₂ := eq80068
       grind)
    | exact superpose eq80068 eq2557
    | (have j0 := eq2557 x
       grind)
    | (have r₁ := eq2557 x
       have r₂ := eq80068
       grind)
    | exact resolve eq2557 eq80068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80068
  have eq684409 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq684242
  have eq684428 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have j1 := eq2557 x
       grind)
    | (have r₁ := eq684409
       have r₂ := eq2557 x
       grind)
    | exact resolve eq684409 eq2557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684409
  have eq684436 : (σ y) = (σ (k y x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq684428
       have i₂ := eq2585 x
       grind)
    | exact superpose eq2585 eq684428
    | exact resolve eq684428 eq2585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684428
  have eq686842 : (k y x) = (τ (σ y)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq684436
       grind)
    | exact superpose eq684436 eq10
    | exact resolve eq10 eq684436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684436
  have eq687330 : y = (k y x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq686842
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq686842
    | exact resolve eq686842 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686842
  have eq687503 : y ≠ y ∨ y = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq56763 y x
       have i₂ := eq687330
       grind)
    | exact superpose eq687330 eq56763
    | (have j0 := eq56763 y x
       grind)
    | (have r₁ := eq56763 y x
       have r₂ := eq687330
       grind)
    | exact resolve eq56763 eq687330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56763 eq687330
  have eq687519 : y = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq687503
  have eq689952 : (σ y) ≠ (σ y) ∨ x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq79976
       have i₂ := eq687519
       grind)
    | exact superpose eq687519 eq79976
    | exact resolve eq79976 eq687519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79976 eq687519
  have eq690020 : x = (M.op x x) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq689952
  have eq690049 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq2557 x
       have i₂ := eq690020
       grind)
    | exact superpose eq690020 eq2557
    | (have j0 := eq2557 x
       grind)
    | (have r₁ := eq2557 x
       have r₂ := eq690020
       grind)
    | exact resolve eq2557 eq690020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690020
  have eq690216 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq690049
  have eq690235 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq2557 x
       grind)
    | (have r₁ := eq690216
       have r₂ := eq2557 x
       grind)
    | exact resolve eq690216 eq2557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2557 eq690216
  have eq690241 : (σ x) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq690235
       have i₂ := eq2585 x
       grind)
    | exact superpose eq2585 eq690235
    | exact resolve eq690235 eq2585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2585 eq690235
  have eq692689 : (M.op x x) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq690241
       grind)
    | exact superpose eq690241 eq10
    | exact resolve eq10 eq690241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq693212 : x = (M.op x x) := by
    first
    | (have i₁ := eq692689
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq692689
    | exact resolve eq692689 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq692689
  have eq693318 : ∀ X0 : G, x ≠ x ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq34 x x
       have i₂ := eq693212
       grind)
    | exact superpose eq693212 eq34
    | (have r₁ := eq34 x x
       have r₂ := eq693212
       grind)
    | exact resolve eq34 eq693212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq693212
  have eq693497 : ∀ X0 : G, (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq693318 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693318
  have eq698732 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56072
       have i₂ := eq693497 y
       grind)
    | exact superpose eq693497 eq56072
    | exact resolve eq56072 eq693497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56072 eq693497
  have eq698741 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq698732
  have eq699130 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq698741
       grind)
    | exact superpose eq698741 eq16
    | exact resolve eq16 eq698741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699142 : (σ x) = (M.op (σ (M.op x x)) (σ y)) := by
    first
    | (have i₁ := eq2825 x (σ y)
       have i₂ := eq698741
       grind)
    | exact superpose eq698741 eq2825
    | exact resolve eq2825 eq698741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2825
  have eq699270 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq699142
       have i₂ := eq690241
       grind)
    | exact superpose eq690241 eq699142
    | exact resolve eq699142 eq690241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699142
  have eq701425 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq698741
       have i₂ := eq699270
       grind)
    | exact superpose eq699270 eq698741
    | exact resolve eq698741 eq699270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698741 eq699270
  have eq704120 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq701425
       grind)
    | exact superpose eq701425 eq10
    | exact resolve eq10 eq701425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701425
  have eq704623 : x = y := by
    first
    | (have i₁ := eq704120
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq704120
    | exact resolve eq704120 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704120
  have eq705297 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq699130
       have i₂ := eq704623
       grind)
    | exact superpose eq704623 eq699130
    | exact resolve eq699130 eq704623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699130 eq704623
  have eq705312 : False := by grind
  exact eq705312
