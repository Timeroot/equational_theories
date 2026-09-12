import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_x_pxy_pyx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
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
  have eq51 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq38 eq15
    | exact resolve eq15 eq38
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
  have eq100 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq45
    | (have j0 := eq45 (M.op x y)
       grind)
    | exact resolve eq45 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq133 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | (have i₁ := eq51 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq51
    | (have j0 := eq51 y
       grind)
    | exact resolve eq51 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
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
  have eq180 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op X0 X1) (σ x)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
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
  have eq184 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28
    | (have j0 := eq28 (σ x) (σ y)
       grind)
    | exact resolve eq28 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 X3) X0) (k X0 X1)) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X2 X3 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq16
    | (have j1 := eq28 X0 X1
       grind)
    | exact resolve eq16 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq41 x
       have i₂ := eq183
       grind)
    | exact superpose eq183 eq41
    | exact resolve eq41 eq183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq183
  have eq197 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq196
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq196
    | exact resolve eq196 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq199 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq197
    | exact resolve eq197 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq203 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq199 eq184
    | exact resolve eq184 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq206 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq203
       have r₂ := eq27
       grind)
    | exact resolve eq203 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq208 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq206 eq27
    | exact resolve eq27 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y X0)) := by
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
  have eq213 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 (σ x) (σ y) X0
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq177
    | (have j0 := eq177 X0 (σ x) (σ y)
       grind)
    | exact resolve eq177 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq233 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq206 eq213
    | exact resolve eq213 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq244 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq233 eq177
    | exact resolve eq177 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 : G, (σ x) = (k (M.op X0 (σ x)) (σ y)) ∨ (σ x) = (M.op X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq244 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq489 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq508 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq28 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq28 X0 X1
       grind)
    | exact resolve eq12 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ y) (M.op X0 (σ x))) ∨ (k (M.op X0 (σ x)) (σ y)) = (M.op (σ y) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq244 eq12
    | (have j0 := eq12 (M.op X0 (σ x)) (σ y)
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq244 X0
       grind)
    | exact resolve eq12 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ x)) ∨ (k (σ y) (σ y)) = (M.op (σ y) (M.op X0 (σ x))) ∨ (k (M.op X0 (σ x)) (σ y)) = (M.op (σ y) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq511 X0
       have i₂ := eq489 sF3
       grind)
    | exact superpose eq489 eq511
    | (have j0 := eq511 X0
       grind)
    | exact resolve eq511 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq544 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq508 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq508 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq508 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq508
  have eq546 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq544 X0 X1
       have i₂ := eq489 X1
       grind)
    | exact superpose eq489 eq544
    | (have j0 := eq544 X0 X1
       grind)
    | exact resolve eq544 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq1078 : (σ x) = (M.op (k (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq244 sF2
       have i₂ := eq489 sF2
       grind)
    | exact superpose eq489 eq244
    | exact resolve eq244 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1102 : (σ y) = (M.op (σ x) (k (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq233 sF3
       have i₂ := eq489 sF3
       grind)
    | exact superpose eq489 eq233
    | exact resolve eq233 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1173 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (σ y) (M.op (k (σ y) (σ y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1102 eq177
    | exact resolve eq177 eq1102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1191 : ∀ X0 : G, (k (σ x) (σ x)) = (M.op (M.op X0 (k (σ x) (σ x))) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1078 eq177
    | exact resolve eq177 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078
  have eq1218 : ∀ X0 : G, (k (σ y) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (k (M.op (k (σ y) (σ y)) X0) (σ y)) = (M.op (M.op (k (σ y) (σ y)) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1173 eq13
    | (have j0 := eq13 (M.op (k (σ y) (σ y)) X0) (σ y)
       grind)
    | exact resolve eq13 eq1173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1173
  have eq1238 : ∀ X0 : G, (k (M.op (k (σ y) (σ y)) X0) (σ y)) = (M.op (M.op (k (σ y) (σ y)) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1218 X0
       grind)
    | (have r₁ := eq1218 X0
       have r₂ := eq489 (σ y)
       grind)
    | exact resolve eq1218 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1218
  have eq2095 : (σ x) = (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1191 eq180
    | exact resolve eq180 eq1191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq1191
  have eq2113 : (σ x) = (M.op (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq206 eq2095
    | exact resolve eq2095 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206 eq2095
  have eq2163 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2113 eq541
    | (have r₁ := eq541 (k (σ x) (σ x))
       have r₂ := eq2113
       grind)
    | exact resolve eq541 eq2113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541
  have eq2170 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (σ x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2113 eq177
    | exact resolve eq177 eq2113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2113
  have eq2178 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2163
  have eq2179 : (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2178
  have eq2183 : (k (σ y) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq199 eq2179
    | exact resolve eq2179 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2179
  have eq2192 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2170 eq2170
    | exact resolve eq2170 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2205 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2170 eq177
    | exact resolve eq177 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2170
  have eq2219 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2192
  have eq2231 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2219
       have i₂ := eq489 sF2
       grind)
    | exact superpose eq489 eq2219
    | exact resolve eq2219 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2219
  have eq2239 : (τ (σ x)) = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2231 eq98
    | exact resolve eq98 eq2231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq2281 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq2239
    | exact resolve eq2239 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2239
  have eq2648 : (σ x) = (M.op (k (σ y) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2183 eq244
    | exact resolve eq244 eq2183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2183
  have eq2664 : (σ x) = (M.op (k (σ y) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq2648
  have eq2755 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq2664 eq1238
    | exact resolve eq1238 eq2664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238 eq2664
  have eq2788 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq2755
  have eq2810 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq2788
    | exact resolve eq2788 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2788
  have eq2824 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq199 eq2810
    | exact resolve eq2810 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq2810
  have eq2831 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2824
       have r₂ := eq27
       grind)
    | exact resolve eq2824 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2824
  have eq2837 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2831 eq233
    | exact resolve eq233 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq2845 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2831 eq2205
    | exact resolve eq2205 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2205
  have eq2847 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2831 eq255
    | exact resolve eq255 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq2848 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2831 eq244
    | exact resolve eq244 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244 eq2831
  have eq2863 : (σ x) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2848
  have eq2864 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq2847
  have eq2866 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq2845
  have eq2874 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq2837
  have eq2877 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2864
       have r₂ := eq208
       grind)
    | exact resolve eq2864 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2864
  have eq2890 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op X0 (σ (M.op x y))) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2863 eq177
    | exact resolve eq177 eq2863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2863
  have eq2933 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2874
       have i₂ := eq28 sF2 sF1
       grind)
    | exact superpose eq28 eq2874
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq2874 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2874
  have eq2960 : (τ (σ x)) = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2877 eq133
    | exact resolve eq133 eq2877
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq2877
  have eq2963 : x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq2960
    | exact resolve eq2960 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2960
  have eq3108 : ∀ X0 : G, (σ (M.op x y)) = (k (M.op X0 (σ (M.op x y))) (σ x)) ∨ x = (M.op x y) ∨ (M.op X0 (σ (M.op x y))) = (M.op (M.op X0 (σ (M.op x y))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2890 X0
       have i₂ := eq28 (M.op X0 sF1) sF2
       grind)
    | exact superpose eq28 eq2890
    | (have j1 := eq28 x y
       grind)
    | exact resolve eq2890 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3120 : ∀ X0 : G, (σ (M.op x y)) = (k (M.op X0 (σ (M.op x y))) (σ x)) ∨ (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2890 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq2890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2890
  have eq3141 : ∀ X0 : G, (σ (M.op x y)) = (k (M.op X0 (σ (M.op x y))) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq3120 eq3108
    | (have j0 := eq3108 X0
       have j1 := eq3120 X0
       grind)
    | exact resolve eq3108 eq3120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3108 eq3120
  have eq3143 : ∀ X0 : G, (σ (M.op x y)) = (k (M.op X0 (σ (M.op x y))) (σ x)) ∨ x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | exact superpose eq2866 eq3141
    | (have j0 := eq3141 X0
       grind)
    | exact resolve eq3141 eq2866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2866 eq3141
  have eq3145 : ∀ X0 : G, (σ (M.op x y)) = (k (M.op X0 (σ (M.op x y))) (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq3143 X0
       grind)
    | (have r₁ := eq3143 X0
       have r₂ := eq208
       grind)
    | exact resolve eq3143 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3143
  have eq3812 : (τ (σ y)) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2933 eq100
    | exact resolve eq100 eq2933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq2933
  have eq3820 : (σ x) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ y = (k x (M.op x y)) := by
    first
    | exact superpose eq32 eq3812
    | exact resolve eq3812 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq3812
  have eq3873 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (k x (M.op x y)) := by
    first
    | exact superpose eq3820 eq3145
    | exact resolve eq3145 eq3820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3145 eq3820
  have eq3892 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (k x (M.op x y)) := by grind
  clear eq3873
  have eq3902 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (k x (M.op x y)) := by
    first
    | exact superpose eq2231 eq3892
    | exact resolve eq3892 eq2231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2231 eq3892
  have eq3907 : y = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq3902
       have r₂ := eq208
       grind)
    | exact resolve eq3902 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq3902
  have eq4856 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op X0 X1) (M.op x y)) x) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2963 eq185
    | (have j0 := eq185 (M.op x y) y x x
       grind)
    | exact resolve eq185 eq2963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5486 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq179 eq4856
    | exact resolve eq4856 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4856
  have eq5589 : (M.op x y) = (k x x) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5486
       have i₂ := eq489 x
       grind)
    | exact superpose eq489 eq5486
    | exact resolve eq5486 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5486
  have eq5596 : x = (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2281 eq5589
    | exact resolve eq5589 eq2281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2281 eq5589
  have eq5597 : (M.op x y) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq5596
  have eq5606 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5597 eq177
    | exact resolve eq177 eq5597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5597
  have eq5624 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq179 eq5606
    | exact resolve eq5606 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq5625 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5606 eq5606
    | exact resolve eq5606 eq5606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5606
  have eq5649 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq5625
  have eq5652 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5649
       have i₂ := eq489 sF0
       grind)
    | exact superpose eq489 eq5649
    | exact resolve eq5649 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5649
  have eq5659 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5624 eq28
    | (have j0 := eq28 x y
       grind)
    | exact resolve eq28 eq5624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5624
  have eq5674 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq5659
  have eq5961 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5674 eq3907
    | exact resolve eq3907 eq5674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3907 eq5674
  have eq5968 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5961
  have eq5982 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2963
       have i₂ := eq5968
       grind)
    | exact superpose eq5968 eq2963
    | exact resolve eq2963 eq5968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2963 eq5968
  have eq5994 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq5982
  have eq5997 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5652 eq5994
    | exact resolve eq5994 eq5652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5652 eq5994
  have eq5998 : x = (M.op x y) := by grind
  clear eq5997
  have eq6002 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5998
       grind)
    | exact superpose eq5998 eq18
    | exact resolve eq18 eq5998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6003 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq5998
       grind)
    | exact superpose eq5998 eq22
    | exact resolve eq22 eq5998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq5998
  have eq6009 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq6003 eq20
    | exact resolve eq20 eq6003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6114 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq6002 eq177
    | exact resolve eq177 eq6002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6116 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq6002 eq178
    | exact resolve eq178 eq6002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178 eq6002
  have eq6238 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq6114 eq6114
    | exact resolve eq6114 eq6114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6114
  have eq6266 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq6238
       have i₂ := eq489 sF0
       grind)
    | exact superpose eq489 eq6238
    | exact resolve eq6238 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6238
  have eq6269 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6266 eq38
    | exact resolve eq38 eq6266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6276 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq6269
    | exact resolve eq6269 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq6269
  have eq6278 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq6009 eq6276
    | exact resolve eq6276 eq6009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6276
  have eq6324 : ∀ X0 : G, (M.op x y) ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op (M.op (M.op x y) X0) (M.op x y)) = (k (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq6116 eq13
    | (have j0 := eq13 (M.op (M.op x y) X0) (M.op x y)
       grind)
    | exact resolve eq13 eq6116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6116
  have eq6340 : ∀ X0 : G, (M.op x y) ≠ (k (M.op x y) (M.op x y)) ∨ (M.op (M.op (M.op x y) X0) (M.op x y)) = (k (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq6324 X0
       have i₂ := eq489 sF0
       grind)
    | exact superpose eq489 eq6324
    | (have j0 := eq6324 X0
       grind)
    | exact resolve eq6324 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6324
  have eq6345 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x y)) = (k (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq6340 X0
       grind)
    | (have r₁ := eq6340 X0
       have r₂ := eq6266
       grind)
    | exact resolve eq6340 eq6266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6266 eq6340
  have eq6959 : (k y (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | exact superpose eq212 eq6345
    | exact resolve eq6345 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6345
  have eq7004 : y = (M.op (M.op x y) (k y (M.op x y))) := by
    first
    | exact superpose eq6959 eq212
    | exact resolve eq212 eq6959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq6959
  have eq7034 : y = (k (M.op x y) (k y (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7004 eq28
    | exact resolve eq28 eq7004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7004
  have eq7491 : (σ y) = (k (σ (M.op x y)) (σ (k y (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7034 eq38
    | exact resolve eq38 eq7034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq7034
  have eq7494 : (σ y) = (k (σ (M.op x y)) (k (σ y) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq42 eq7491
    | exact resolve eq7491 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq7491
  have eq7496 : (σ y) = (k (σ x) (k (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6009 eq7494
    | exact resolve eq7494 eq6009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7494
  have eq7498 : (σ y) = (k (σ x) (k (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7496
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7496
    | exact resolve eq7496 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7496
  have eq11484 : (σ x) = (M.op (k (σ x) (σ x)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq218 sF2
       have i₂ := eq489 sF2
       grind)
    | exact superpose eq489 eq218
    | exact resolve eq218 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq11534 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6278 eq11484
    | exact resolve eq11484 eq6278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11484
  have eq11546 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) := by
    intro X0
    first
    | exact superpose eq11534 eq177
    | exact resolve eq177 eq11534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11534
  have eq11569 : ∀ X0 : G, (σ x) = (M.op (k X0 (σ x)) (σ x)) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11546 X0
       have i₂ := eq28 X0 sF2
       grind)
    | exact superpose eq28 eq11546
    | (have j1 := eq28 X0 (σ x)
       grind)
    | exact resolve eq11546 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11596 : ∀ X1 : G, (σ x) = (M.op (σ x) (k (σ x) X1)) ∨ (σ x) = (M.op (σ x) X1) := by
    intro X1
    first
    | exact superpose eq11546 eq185
    | (have j0 := eq185 (σ x) (k (σ x) X1) x x
       grind)
    | exact resolve eq185 eq11546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq11605 : ∀ X0 : G, (σ x) = (k (M.op X0 (σ x)) (σ x)) ∨ (σ x) = (M.op X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq11546 eq28
    | exact resolve eq28 eq11546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq11546
  have eq12467 : ∀ X0 X1 : G, (k X1 (σ x)) = (M.op (M.op X0 (k X1 (σ x))) (σ x)) ∨ (M.op X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq11569 eq177
    | (have j1 := eq11569 X1
       grind)
    | exact resolve eq177 eq11569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq11569
  have eq12508 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (k (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq7498 eq11596
    | (have j0 := eq11596 (σ y)
       grind)
    | exact resolve eq11596 eq7498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11596
  have eq12572 : (σ x) = (M.op (σ x) (k (σ y) (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq12508
    | exact resolve eq12508 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12508
  have eq13937 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12572 eq12467
    | (have j0 := eq12467 x (σ y)
       grind)
    | exact resolve eq12467 eq12572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12467 eq12572
  have eq14005 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13937
       have i₂ := eq489 sF2
       grind)
    | exact superpose eq489 eq13937
    | exact resolve eq13937 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13937
  have eq14008 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6278 eq14005
    | exact resolve eq14005 eq6278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14005
  have eq15572 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14008 eq11605
    | exact resolve eq11605 eq14008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11605
  have eq15573 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq14008 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq14008
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq14008
       grind)
    | exact resolve eq12 eq14008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14008
  have eq15598 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15573
  have eq15599 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15572
  have eq15604 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15598
       have i₂ := eq489 sF2
       grind)
    | exact superpose eq489 eq15598
    | exact resolve eq15598 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489 eq15598
  have eq15610 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6278 eq15604
    | exact resolve eq15604 eq6278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15604
  have eq15614 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq15610
    | exact resolve eq15610 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15610
  have eq15615 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq15614
  have eq15616 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq15615
    | exact resolve eq15615 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15615
  have eq15617 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15599 eq15616
    | exact resolve eq15616 eq15599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15599 eq15616
  have eq15618 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6278 eq15617
    | exact resolve eq15617 eq6278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15617
  have eq15619 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15618
  have eq15627 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15619 eq7498
    | exact resolve eq7498 eq15619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7498
  have eq15664 : (σ x) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15619 eq546
    | (have j0 := eq546 (σ y) (σ x)
       grind)
    | exact resolve eq546 eq15619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq15619
  have eq15670 : (σ y) = (k (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15627
  have eq15672 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6278 eq15664
    | exact resolve eq15664 eq6278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15664
  have eq15673 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15672
  have eq15682 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6278 eq15670
    | exact resolve eq15670 eq6278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15670
  have eq15686 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq15673
    | exact resolve eq15673 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq15673
  have eq15687 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ y = (M.op x y) := by grind
  clear eq15686
  have eq15690 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq15687
       have r₂ := eq15682
       grind)
    | exact resolve eq15687 eq15682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15682 eq15687
  have eq15692 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15690 eq27
    | exact resolve eq27 eq15690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15690
  have eq15747 : y = (M.op x y) := by
    first
    | (have r₁ := eq15692
       have r₂ := eq6009
       grind)
    | exact resolve eq15692 eq6009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15692
  have eq15752 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq15747
       grind)
    | exact superpose eq15747 eq24
    | exact resolve eq24 eq15747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq15747
  have eq15823 : (σ x) = (σ y) := by
    first
    | exact superpose eq6003 eq15752
    | exact resolve eq15752 eq6003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6003 eq15752
  have eq15848 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15823 eq184
    | exact resolve eq184 eq15823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq15823
  have eq15967 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6278 eq15848
    | exact resolve eq15848 eq6278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6278 eq15848
  have eq15968 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15967
  have eq15998 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq15968 eq27
    | exact resolve eq27 eq15968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq15968
  have eq16055 : False := by grind
  exact eq16055

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxy_pyy_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq62 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
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
  have eq67 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X1 (M.op X2 X0) (M.op X0 x)
       have i₂ := eq61 X2 X0 x
       grind)
    | exact superpose eq61 eq61
    | exact resolve eq61 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X3 X0) X1 X2 (M.op X0 x)
       have i₂ := eq61 X3 X0 x
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 : G, (k X1 (M.op X0 X0)) = (M.op X1 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq61 X0 X0 X0
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq116 (σ X0)
       grind)
    | exact superpose eq116 eq15
    | exact resolve eq15 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq116 X0
       grind)
    | exact superpose eq116 eq119
    | exact resolve eq119 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq147 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0) (σ X0)
       have i₂ := eq130 X0
       grind)
    | exact superpose eq130 eq61
    | exact resolve eq61 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ X0) (σ X0) X1
       have i₂ := eq130 X0
       grind)
    | exact superpose eq130 eq61
    | exact resolve eq61 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ X0) (σ X0) x
       have i₂ := eq130 X0
       grind)
    | exact superpose eq130 eq62
    | exact resolve eq62 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq153 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq130 X0
       grind)
    | exact superpose eq130 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq305 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (M.op X0 X0)) ∨ (k (M.op (σ (M.op X0 X0)) X1) (σ X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op (σ (M.op X0 X0)) X1) (σ X0)
       have i₂ := eq149 X0 X1
       grind)
    | exact superpose eq149 eq12
    | (have j0 := eq12 (M.op (σ (M.op X0 X0)) X1) (σ X0)
       grind)
    | exact resolve eq12 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq312 : ∀ X0 X1 : G, (k (M.op (σ (M.op X0 X0)) X1) (σ X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq305 X0 X1
       grind)
    | (have r₁ := eq305 X0 X1
       have r₂ := eq130 X0
       grind)
    | exact resolve eq305 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq1709 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq1726 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1709 X0 X1
       have i₂ := eq130 X1
       grind)
    | exact superpose eq130 eq1709
    | (have j0 := eq1709 X0 X1
       grind)
    | exact resolve eq1709 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1709
  have eq2749 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1726 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1726
    | exact resolve eq1726 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726
  have eq2852 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2749 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq2749
    | (have j0 := eq2749 X0 X1
       grind)
    | exact resolve eq2749 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2749
  have eq2863 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2852 X0 X1
       have j1 := eq153 X1 X0
       grind)
    | (have r₁ := eq2852 X1 X0
       have r₂ := eq153 X0 X1
       grind)
    | (have r₁ := eq2852 (σ X0) (M.op X0 X0)
       have r₂ := eq153 X0 (σ (M.op X0 X0))
       grind)
    | exact resolve eq2852 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq2852
  have eq2867 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2863 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2863
    | exact resolve eq2863 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2884 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2863 (σ X0) X1
       grind)
    | exact superpose eq2863 eq15
    | (have j1 := eq2863 (σ X0) X1
       grind)
    | exact resolve eq15 eq2863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2863
  have eq2939 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq2867 X1 (τ X0)
       grind)
    | exact superpose eq2867 eq17
    | (have j1 := eq2867 X1 (τ X0)
       grind)
    | exact resolve eq17 eq2867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq2867
  have eq3119 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2939 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2939
    | exact resolve eq2939 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2939
  have eq3212 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3119 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3119
    | (have j0 := eq3119 X0 X1
       grind)
    | exact resolve eq3119 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3119
  have eq3563 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2884 x y
       grind)
    | exact superpose eq2884 eq16
    | (have j1 := eq2884 x y
       grind)
    | exact resolve eq16 eq2884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3628 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2884 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2884
  have eq3896 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3563
       have i₂ := eq3212 x y
       grind)
    | exact superpose eq3212 eq3563
    | (have j1 := eq3212 (σ x) (σ y)
       grind)
    | (have r₁ := eq3563
       have r₂ := eq3212 x y
       grind)
    | exact resolve eq3563 eq3212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3897 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3896
  have eq3904 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61 X0 x y
       have i₂ := eq3897
       grind)
    | exact superpose eq3897 eq61
    | exact resolve eq61 eq3897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3905 : ∀ X0 : G, y = (M.op y (M.op y X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61 x y X0
       have i₂ := eq3897
       grind)
    | exact superpose eq3897 eq61
    | exact resolve eq61 eq3897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3897
  have eq3938 : y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3905 (M.op y x)
       have i₂ := eq3905 x
       grind)
    | exact superpose eq3905 eq3905
    | exact resolve eq3905 eq3905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3905
  have eq3956 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq3938
  have eq3963 : (σ y) = (M.op (σ y) (σ (M.op y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq147 y (σ x)
       have i₂ := eq3956
       grind)
    | exact superpose eq3956 eq147
    | exact resolve eq147 eq3956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq3969 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq61 (σ x) (σ y) X0
       have i₂ := eq3956
       grind)
    | exact superpose eq3956 eq61
    | exact resolve eq61 eq3956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq3956
  have eq4165 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq3969 (σ (M.op y y))
       have i₂ := eq3963
       grind)
    | exact superpose eq3963 eq3969
    | exact resolve eq3969 eq3963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3963 eq3969
  have eq4189 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq4165
  have eq4195 : y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4189
       have i₂ := eq130 y
       grind)
    | exact superpose eq130 eq4189
    | exact resolve eq4189 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4189
  have eq4243 : ∀ X0 X1 : G, (σ y) = (σ (M.op y y)) ∨ y = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq69 y X1 x y
       have i₂ := eq4195
       grind)
    | exact superpose eq4195 eq69
    | exact resolve eq69 eq4195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq4195
  have eq4532 : ∀ X0 X1 : G, (M.op y y) = (τ (σ y)) ∨ y = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq4243 X0 X1
       grind)
    | exact superpose eq4243 eq10
    | (have j1 := eq4243 X0 X1
       grind)
    | exact resolve eq10 eq4243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4243
  have eq4604 : ∀ X0 X1 : G, y = (M.op y y) ∨ y = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq4532 X0 X1
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4532
    | (have j0 := eq4532 X0 X1
       grind)
    | exact resolve eq4532 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4532
  have eq4652 : ∀ X0 X1 X2 : G, y = (M.op (M.op X0 y) y) ∨ y = (M.op (M.op (M.op X1 X2) y) y) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 y X1 y
       have i₂ := eq4604 X0 X1
       grind)
    | exact superpose eq4604 eq67
    | (have j1 := eq4604 X1 X2
       grind)
    | exact resolve eq67 eq4604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4604
  have eq4719 : ∀ X0 X1 : G, y ≠ y ∨ y = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have j0 := eq4652 (M.op X0 X1) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4652
  have eq4720 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 X1) y) y) := by
    intro X0 X1
    first
    | (have j0 := eq4719 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4719
  have eq4779 : y = (M.op y y) := by
    first
    | (have i₁ := eq4720 (M.op x x) y
       have i₂ := eq4720 x x
       grind)
    | exact superpose eq4720 eq4720
    | exact resolve eq4720 eq4720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4796 : ∀ X2 : G, y = (M.op (M.op X2 y) y) := by
    intro X2
    first
    | (have i₁ := eq67 y x (M.op (M.op x x) y)
       have i₂ := eq4720 x x
       grind)
    | exact superpose eq4720 eq67
    | exact resolve eq67 eq4720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4720
  have eq4811 : ∀ X0 : G, y ≠ (M.op y X0) ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq115 y x
       have i₂ := eq4779
       grind)
    | exact superpose eq4779 eq115
    | exact resolve eq115 eq4779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq4831 : ∀ X0 : G, (k (M.op (σ y) X0) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq312 y x
       have i₂ := eq4779
       grind)
    | exact superpose eq4779 eq312
    | exact resolve eq312 eq4779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312
  have eq4914 : ∀ X0 : G, y ≠ y ∨ (M.op y y) = (M.op y (M.op X0 y)) ∨ (M.op y y) = (k (M.op X0 y) y) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op X0 y) y
       have i₂ := eq4796 X0
       grind)
    | exact superpose eq4796 eq13
    | (have j0 := eq13 (M.op X0 y) y
       grind)
    | (have r₁ := eq13 (M.op x y) y
       have r₂ := eq4796 x
       grind)
    | exact resolve eq13 eq4796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4796
  have eq4928 : ∀ X0 : G, (M.op y y) = (M.op y (M.op X0 y)) ∨ (M.op y y) = (k (M.op X0 y) y) := by
    intro X0
    first
    | (have j0 := eq4914 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4914
  have eq4929 : ∀ X0 : G, y = (M.op y (M.op X0 y)) ∨ (M.op y y) = (k (M.op X0 y) y) := by
    intro X0
    first
    | (have i₁ := eq4928 X0
       have i₂ := eq4779
       grind)
    | exact superpose eq4779 eq4928
    | (have j0 := eq4928 X0
       grind)
    | exact resolve eq4928 eq4779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4928
  have eq4930 : ∀ X0 : G, y = (k (M.op X0 y) y) ∨ y = (M.op y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq4929 X0
       have i₂ := eq4779
       grind)
    | exact superpose eq4779 eq4929
    | (have j0 := eq4929 X0
       grind)
    | exact resolve eq4929 eq4779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4929
  have eq5717 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ (M.op X0 y)) (σ y)) ∨ y = (M.op y (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq3628 (M.op X0 y) y
       have i₂ := eq4930 X0
       grind)
    | exact superpose eq4930 eq3628
    | (have j0 := eq3628 (M.op X0 y) y
       have j1 := eq4930 X0
       grind)
    | exact resolve eq3628 eq4930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3628 eq4930
  have eq5722 : ∀ X0 : G, y = (M.op y (M.op X0 y)) ∨ (σ y) = (M.op (σ (M.op X0 y)) (σ y)) := by
    intro X0
    first
    | (have j0 := eq5717 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5717
  have eq5737 : ∀ X0 : G, (k (τ (M.op (σ y) X0)) y) = (τ (M.op (M.op (σ y) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq22 (M.op (σ y) X0) y
       have i₂ := eq4831 X0
       grind)
    | exact superpose eq4831 eq22
    | exact resolve eq22 eq4831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4831
  have eq6345 : ∀ X0 : G, (τ (M.op X0 (σ y))) = (k (τ (M.op (σ y) (M.op X0 (σ y)))) y) := by
    intro X0
    first
    | (have i₁ := eq5737 (M.op X0 (σ y))
       have i₂ := eq67 (σ y) (σ y) X0
       grind)
    | exact superpose eq67 eq5737
    | exact resolve eq5737 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq5737
  have eq7136 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5722 (M.op x x)
       have i₂ := eq3904 x
       grind)
    | exact superpose eq3904 eq5722
    | exact resolve eq5722 eq3904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5722
  have eq7181 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7136
  have eq7195 : y ≠ y ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4811 x
       have i₂ := eq7181
       grind)
    | exact superpose eq7181 eq4811
    | (have j0 := eq4811 x
       grind)
    | (have r₁ := eq4811 x
       have r₂ := eq7181
       grind)
    | exact resolve eq4811 eq7181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4811
  have eq7197 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3904 y
       have i₂ := eq7181
       grind)
    | exact superpose eq7181 eq3904
    | exact resolve eq3904 eq7181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3904 eq7181
  have eq7217 : x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7197
  have eq7218 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7195
  have eq7223 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq7217
       have i₂ := eq4779
       grind)
    | exact superpose eq4779 eq7217
    | exact resolve eq7217 eq4779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7217
  have eq7229 : (σ x) = (M.op (σ (M.op x x)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq148 x (σ y)
       have i₂ := eq7223
       grind)
    | exact superpose eq7223 eq148
    | exact resolve eq148 eq7223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq7223
  have eq7296 : (τ (σ x)) = (k (τ (M.op (σ y) (σ x))) y) ∨ x = y := by
    first
    | (have i₁ := eq6345 (σ (M.op x x))
       have i₂ := eq7229
       grind)
    | exact superpose eq7229 eq6345
    | exact resolve eq6345 eq7229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6345 eq7229
  have eq7326 : x = (k (τ (M.op (σ y) (σ x))) y) ∨ x = y := by
    first
    | (have i₁ := eq7296
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq7296
    | exact resolve eq7296 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7296
  have eq7676 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3563
       have i₂ := eq7218
       grind)
    | exact superpose eq7218 eq3563
    | exact resolve eq3563 eq7218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3563 eq7218
  have eq7681 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7676
  have eq7682 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq7681
  have eq7685 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7682
       grind)
    | exact superpose eq7682 eq16
    | exact resolve eq16 eq7682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7697 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq7682
       grind)
    | exact superpose eq7682 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq7682
       grind)
    | exact resolve eq13 eq7682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7682
  have eq7715 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq7697
  have eq7719 : (σ (M.op y y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq7715
       have i₂ := eq130 y
       grind)
    | exact superpose eq130 eq7715
    | exact resolve eq7715 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7715
  have eq7732 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq7719
       have i₂ := eq4779
       grind)
    | exact superpose eq4779 eq7719
    | exact resolve eq7719 eq4779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7719
  have eq7737 : (σ (k x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7732
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq7732
    | exact resolve eq7732 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7732
  have eq7740 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7737
       have i₂ := eq130 y
       grind)
    | exact superpose eq130 eq7737
    | exact resolve eq7737 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7737
  have eq7742 : (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7740
       have i₂ := eq4779
       grind)
    | exact superpose eq4779 eq7740
    | exact resolve eq7740 eq4779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7740
  have eq8725 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq3212 x y
       have i₂ := eq7742
       grind)
    | exact superpose eq7742 eq3212
    | (have j0 := eq3212 x y
       grind)
    | exact resolve eq3212 eq7742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3212 eq7742
  have eq8786 : y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq8725
       have r₂ := eq7685
       grind)
    | exact resolve eq8725 eq7685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8725
  have eq8814 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq7685
       have i₂ := eq8786
       grind)
    | exact superpose eq8786 eq7685
    | exact resolve eq7685 eq8786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7685 eq8786
  have eq8846 : (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq8814
  have eq8855 : x = (k (τ (σ y)) y) ∨ x = y := by
    first
    | (have i₁ := eq7326
       have i₂ := eq8846
       grind)
    | exact superpose eq8846 eq7326
    | exact resolve eq7326 eq8846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7326 eq8846
  have eq8919 : x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq8855
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq8855
    | exact resolve eq8855 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8855
  have eq8937 : x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq8919
       have i₂ := eq116 y
       grind)
    | exact superpose eq116 eq8919
    | exact resolve eq8919 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq8919
  have eq8947 : x = y ∨ x = y := by
    first
    | (have i₁ := eq8937
       have i₂ := eq4779
       grind)
    | exact superpose eq4779 eq8937
    | exact resolve eq8937 eq4779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4779 eq8937
  have eq8948 : x = y := by grind
  clear eq8947
  have eq8958 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8948
       grind)
    | exact superpose eq8948 eq16
    | exact resolve eq16 eq8948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8948
  have eq9065 : False := by grind
  exact eq9065

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyx_y_pyx_x_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq115 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (M.op (M.op X0 X0) X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq61 X0 X0 X0
       grind)
    | exact superpose eq61 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq116 (σ X0)
       grind)
    | exact superpose eq116 eq15
    | exact resolve eq15 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq130 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq119 X0
       have i₂ := eq116 X0
       grind)
    | exact superpose eq116 eq119
    | exact resolve eq119 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq119
  have eq153 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq130 X0
       grind)
    | exact superpose eq130 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2045 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq2108 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2045 X0 X1
       have i₂ := eq130 X0
       grind)
    | exact superpose eq130 eq2045
    | (have j0 := eq2045 X0 X1
       grind)
    | exact resolve eq2045 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2045
  have eq3991 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2108 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2108
    | exact resolve eq2108 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2108
  have eq4144 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3991 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq3991
    | (have j0 := eq3991 X0 X1
       grind)
    | exact resolve eq3991 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3991
  have eq4171 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq4144 X0 X1
       have j1 := eq153 X1 X0
       grind)
    | (have r₁ := eq4144 X1 X0
       have r₂ := eq153 X0 X1
       grind)
    | exact resolve eq4144 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4144
  have eq4218 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4171 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4171
    | exact resolve eq4171 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4256 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq4171 (σ X1) X0
       grind)
    | exact superpose eq4171 eq15
    | (have j1 := eq4171 (σ X1) X0
       grind)
    | exact resolve eq15 eq4171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4171
  have eq4383 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq4218 X0 (τ X1)
       grind)
    | exact superpose eq4218 eq17
    | (have j1 := eq4218 X0 (τ X1)
       grind)
    | exact resolve eq17 eq4218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq4724 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4383 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4383
    | exact resolve eq4383 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4383
  have eq4891 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4724 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4724
    | (have j0 := eq4724 X0 X1
       grind)
    | exact resolve eq4724 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4724
  have eq6725 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4256 x y
       grind)
    | exact superpose eq4256 eq16
    | (have j1 := eq4256 x y
       grind)
    | exact resolve eq16 eq4256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4256
  have eq7531 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6725
       have i₂ := eq4891 y x
       grind)
    | exact superpose eq4891 eq6725
    | (have j1 := eq4891 (σ y) (σ x)
       grind)
    | (have r₁ := eq6725
       have r₂ := eq4891 y x
       grind)
    | exact resolve eq6725 eq4891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4891
  have eq7532 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq7531
  have eq7539 : ∀ X0 : G, x = (M.op (M.op X0 x) x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq61 X0 x y
       have i₂ := eq7532
       grind)
    | exact superpose eq7532 eq61
    | exact resolve eq61 eq7532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7532
  have eq7554 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7539 (M.op x x)
       have i₂ := eq7539 x
       grind)
    | exact superpose eq7539 eq7539
    | exact resolve eq7539 eq7539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7539
  have eq7579 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq7554
  have eq7594 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ x)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq61 X0 (σ x) (σ y)
       have i₂ := eq7579
       grind)
    | exact superpose eq7579 eq61
    | exact resolve eq61 eq7579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq7579
  have eq8173 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq7594 (M.op x (σ x))
       have i₂ := eq7594 x
       grind)
    | exact superpose eq7594 eq7594
    | exact resolve eq7594 eq7594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7594
  have eq8204 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq8173
  have eq8212 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq8204
       have i₂ := eq130 x
       grind)
    | exact superpose eq130 eq8204
    | exact resolve eq8204 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq8204
  have eq8247 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq8212
       grind)
    | exact superpose eq8212 eq10
    | exact resolve eq10 eq8212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8212
  have eq8351 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq8247
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8247
    | exact resolve eq8247 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8247
  have eq8352 : x = (M.op x x) := by grind
  clear eq8351
  have eq8364 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq115 x x
       have i₂ := eq8352
       grind)
    | exact superpose eq8352 eq115
    | exact resolve eq115 eq8352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq8464 : ∀ X0 : G, (M.op x X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq8364 X0
       have j1 := eq4218 x X0
       grind)
    | (have r₁ := eq8364 x
       have r₂ := eq4218 x x
       grind)
    | exact resolve eq8364 eq4218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4218 eq8364
  have eq8595 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq6725
       have i₂ := eq8464 y
       grind)
    | exact superpose eq8464 eq6725
    | exact resolve eq6725 eq8464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6725
  have eq8596 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8595
  have eq8619 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8596
       grind)
    | exact superpose eq8596 eq16
    | exact resolve eq16 eq8596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8620 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq153 x (σ y)
       have i₂ := eq8596
       grind)
    | exact superpose eq8596 eq153
    | exact resolve eq153 eq8596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq8596
  have eq8656 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq8620
       have i₂ := eq8352
       grind)
    | exact superpose eq8352 eq8620
    | exact resolve eq8620 eq8352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8352 eq8620
  have eq8657 : (σ x) = (k (σ y) (σ x)) := by grind
  clear eq8656
  have eq8670 : (σ x) = (σ (k y x)) := by
    first
    | (have i₁ := eq8657
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq8657
    | exact resolve eq8657 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8657
  have eq8679 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq8670
       have i₂ := eq8464 y
       grind)
    | exact superpose eq8464 eq8670
    | exact resolve eq8670 eq8464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8464 eq8670
  have eq8685 : False := by grind
  exact eq8685

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq117 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq117 (σ X0)
       grind)
    | exact superpose eq117 eq15
    | exact resolve eq15 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq120 X0
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq120
    | exact resolve eq120 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq120
  have eq154 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq711 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq694 X0 X1
       have i₂ := eq131 X1
       grind)
    | exact superpose eq131 eq694
    | (have j0 := eq694 X0 X1
       grind)
    | exact resolve eq694 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq2785 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq711 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq711
    | exact resolve eq711 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq2855 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2785 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq2785
    | (have j0 := eq2785 X0 X1
       grind)
    | exact resolve eq2785 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2785
  have eq2864 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2855 X0 X1
       have j1 := eq154 X1 X0
       grind)
    | (have r₁ := eq2855 X1 X0
       have r₂ := eq154 X0 X1
       grind)
    | (have r₁ := eq2855 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq154 X0 X1
       grind)
    | exact resolve eq2855 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq2855
  have eq2866 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2864 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2864
    | exact resolve eq2864 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2884 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2864 (σ X0) X1
       grind)
    | exact superpose eq2864 eq15
    | (have j1 := eq2864 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq2864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2864
  have eq2923 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq2866 (τ X1) X0
       grind)
    | exact superpose eq2866 eq19
    | (have j1 := eq2866 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq2866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq2866
  have eq3089 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2923 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2923
    | exact resolve eq2923 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2923
  have eq3156 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3089 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3089
    | (have j0 := eq3089 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq3089 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3089
  have eq3397 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2884 x y
       grind)
    | exact superpose eq2884 eq16
    | (have j1 := eq2884 x y
       grind)
    | exact resolve eq16 eq2884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2884
  have eq3442 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3397
       have i₂ := eq3156 y x
       grind)
    | exact superpose eq3156 eq3397
    | (have j1 := eq3156 (σ x) (σ y)
       grind)
    | (have r₁ := eq3397
       have r₂ := eq3156 y x
       grind)
    | (have r₁ := eq3397
       have r₂ := eq3156 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3397
       have r₂ := eq3156 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3397 eq3156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3156 eq3397
  have eq3443 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq3442
  have eq3446 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3443
       grind)
    | exact superpose eq3443 eq16
    | exact resolve eq16 eq3443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3443
  have eq3447 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq3446
       have r₂ := eq131 x
       grind)
    | exact resolve eq3446 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3446
  have eq3448 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3447
       grind)
    | exact superpose eq3447 eq16
    | exact resolve eq16 eq3447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3449 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3447
       grind)
    | exact superpose eq3447 eq10
    | exact resolve eq10 eq3447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3447
  have eq3505 : x = y := by
    first
    | (have i₁ := eq3449
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3449
    | exact resolve eq3449 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3449
  have eq3506 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3448
       have i₂ := eq131 x
       grind)
    | exact superpose eq131 eq3448
    | exact resolve eq3448 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq3448
  have eq3507 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3506
       have i₂ := eq3505
       grind)
    | exact superpose eq3505 eq3506
    | exact resolve eq3506 eq3505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3505 eq3506
  have eq3508 : False := by grind
  exact eq3508

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if X = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxy_x_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq117 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq117 (σ X0)
       grind)
    | exact superpose eq117 eq15
    | exact resolve eq15 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq120 X0
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq120
    | exact resolve eq120 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq120
  have eq154 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq711 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq694 X0 X1
       have i₂ := eq131 X1
       grind)
    | exact superpose eq131 eq694
    | (have j0 := eq694 X0 X1
       grind)
    | exact resolve eq694 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694
  have eq2785 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq711 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq711
    | exact resolve eq711 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq2855 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2785 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq2785
    | (have j0 := eq2785 X0 X1
       grind)
    | exact resolve eq2785 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2785
  have eq2864 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2855 X0 X1
       have j1 := eq154 X1 X0
       grind)
    | (have r₁ := eq2855 X1 X0
       have r₂ := eq154 X0 X1
       grind)
    | (have r₁ := eq2855 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq154 X0 X1
       grind)
    | exact resolve eq2855 eq154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154 eq2855
  have eq2866 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2864 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2864
    | exact resolve eq2864 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2884 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq2864 (σ X0) X1
       grind)
    | exact superpose eq2864 eq15
    | (have j1 := eq2864 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq2864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2864
  have eq2923 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq2866 (τ X1) X0
       grind)
    | exact superpose eq2866 eq19
    | (have j1 := eq2866 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq2866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq2866
  have eq3089 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2923 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2923
    | exact resolve eq2923 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2923
  have eq3156 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3089 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3089
    | (have j0 := eq3089 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq3089 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3089
  have eq3397 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2884 x y
       grind)
    | exact superpose eq2884 eq16
    | (have j1 := eq2884 x y
       grind)
    | exact resolve eq16 eq2884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2884
  have eq3442 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq3397
       have i₂ := eq3156 y x
       grind)
    | exact superpose eq3156 eq3397
    | (have j1 := eq3156 (σ x) (σ y)
       grind)
    | (have r₁ := eq3397
       have r₂ := eq3156 y x
       grind)
    | (have r₁ := eq3397
       have r₂ := eq3156 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3397
       have r₂ := eq3156 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3397 eq3156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3156 eq3397
  have eq3443 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq3442
  have eq3446 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3443
       grind)
    | exact superpose eq3443 eq16
    | exact resolve eq16 eq3443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3443
  have eq3447 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq3446
       have r₂ := eq131 x
       grind)
    | exact resolve eq3446 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3446
  have eq3448 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3447
       grind)
    | exact superpose eq3447 eq16
    | exact resolve eq16 eq3447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3449 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq3447
       grind)
    | exact superpose eq3447 eq10
    | exact resolve eq10 eq3447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3447
  have eq3505 : x = y := by
    first
    | (have i₁ := eq3449
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3449
    | exact resolve eq3449 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3449
  have eq3506 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3448
       have i₂ := eq131 x
       grind)
    | exact superpose eq131 eq3448
    | exact resolve eq3448 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq3448
  have eq3507 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq3506
       have i₂ := eq3505
       grind)
    | exact superpose eq3505 eq3506
    | exact resolve eq3506 eq3505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3505 eq3506
  have eq3508 : False := by grind
  exact eq3508

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if X = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyy_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq62 : ∀ X0 X4 X5 : G, (M.op (M.op X0 X4) (M.op X4 X5)) = X4 := by
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
  have eq63 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
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
  have eq117 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq117 (σ X0)
       grind)
    | exact superpose eq117 eq15
    | exact resolve eq15 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq117 (τ X0)
       grind)
    | exact superpose eq117 eq32
    | exact resolve eq32 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq129 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq122 X0
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq122
    | exact resolve eq122 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq131 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq120 X0
       have i₂ := eq117 X0
       grind)
    | exact superpose eq117 eq120
    | exact resolve eq120 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq120
  have eq149 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ X0) (σ X0) X1
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq62
    | exact resolve eq62 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X0) (σ X0) x
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq63
    | exact resolve eq63 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq164 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 (τ X0) (τ X0)
       have i₂ := eq129 X0
       grind)
    | exact superpose eq129 eq62
    | exact resolve eq62 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (M.op (σ X0) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op (σ X0) X1) (σ (M.op X0 X0))
       have i₂ := eq149 X0 X1
       grind)
    | exact superpose eq149 eq12
    | (have j0 := eq12 (M.op (σ X0) X1) (σ (M.op X0 X0))
       grind)
    | exact resolve eq12 eq149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq222 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (M.op (σ X0) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq215 X0 X1
       have i₂ := eq131 (M.op X0 X0)
       grind)
    | exact superpose eq131 eq215
    | (have j0 := eq215 X0 X1
       grind)
    | exact resolve eq215 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq229 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (M.op (σ X0) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq222 X0 X1
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq222 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq222
    | (have j0 := eq222 X0 X1
       grind)
    | exact resolve eq222 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq230 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (k (M.op (σ X0) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq229 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq233 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (k (M.op (σ X0) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq230 X0 X1
       have i₂ := eq131 (M.op X0 X0)
       grind)
    | exact superpose eq131 eq230
    | exact resolve eq230 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq234 : ∀ X0 X1 : G, (σ X0) = (k (M.op (σ X0) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq233 X0 X1
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq233 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq233
    | exact resolve eq233 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq244 : ∀ X0 X1 : G, (σ (τ X0)) = (k (M.op (σ (τ X0)) X1) (σ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq234 (τ X0) X1
       have i₂ := eq129 X0
       grind)
    | exact superpose eq129 eq234
    | exact resolve eq234 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234
  have eq247 : ∀ X0 X1 : G, (σ (τ X0)) = (k (M.op (σ (τ X0)) X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq244 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq244
    | exact resolve eq244 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq253 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq247 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq247
    | exact resolve eq247 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq269 : ∀ X0 X1 : G, (τ X0) = (k (M.op (τ X0) X1) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq253 (τ X0) X1
       have i₂ := eq129 X0
       grind)
    | exact superpose eq129 eq253
    | exact resolve eq253 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq253
  have eq388 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) X1)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq19 (M.op X0 X0) (M.op (τ X0) X1)
       have i₂ := eq269 X0 X1
       grind)
    | exact superpose eq269 eq19
    | exact resolve eq19 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq269
  have eq389 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) X1)) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq388
    | exact resolve eq388 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq619 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ (M.op (τ X0) X1))) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X0) (σ (M.op (τ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq389 X0 X1
       have i₂ := eq14 (σ (M.op (τ X0) X1)) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq389
    | (have j1 := eq14 (M.op (M.op X0 X0) (σ (M.op (τ X0) X1))) X0
       grind)
    | exact resolve eq389 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq634 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ (M.op (τ X0) X1))) = X0 ∨ (M.op (M.op X0 X0) (σ (M.op (τ X0) X1))) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq619 X0 X1
       have i₂ := eq62 X0 X0 X0
       grind)
    | (have i₁ := eq619 X0 X1
       have i₂ := eq62 X0 (M.op (M.op X0 X0) (M.op X0 X0)) x
       grind)
    | exact superpose eq62 eq619
    | (have j0 := eq619 X0 X1
       grind)
    | exact resolve eq619 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq635 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ (M.op (τ X0) X1))) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq634 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq11674 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) (σ X0)) (σ (M.op X0 X1))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq635 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq635
    | exact resolve eq635 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq11735 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X1))) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11674 X0 X1
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq11674
    | (have j0 := eq11674 X0 X1
       grind)
    | exact resolve eq11674 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11674
  have eq11743 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X1))) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11735 X0 X1
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq11735
    | (have j0 := eq11735 X0 X1
       grind)
    | exact resolve eq11735 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11735
  have eq14579 : ∀ X0 X1 X2 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (M.op (σ (M.op X0 X1)) X2)) ∨ (σ (M.op X0 X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (σ (M.op X0 X0)) (σ (M.op X0 X1)) X2
       have i₂ := eq11743 X0 X1
       grind)
    | exact superpose eq11743 eq62
    | (have j1 := eq11743 X0 X1
       grind)
    | exact resolve eq62 eq11743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq11743
  have eq54351 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (σ (M.op X1 (τ X0))) (M.op (σ (τ X0)) X2)) ∨ (σ (τ X0)) = (σ (M.op (M.op X1 (τ X0)) (M.op X1 (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14579 (M.op X1 (τ X0)) (τ (M.op X0 X0)) X2
       have i₂ := eq164 X0 X1
       grind)
    | exact superpose eq164 eq14579
    | exact resolve eq14579 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq14579
  have eq54610 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X1 (τ X0))) (M.op X0 X2)) = X0 ∨ (σ (τ X0)) = (σ (M.op (M.op X1 (τ X0)) (M.op X1 (τ X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54351 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq54351
    | (have j0 := eq54351 X0 X1 X2
       grind)
    | exact resolve eq54351 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54351
  have eq54683 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X1 (τ X0)) (M.op X1 (τ X0)))) = X0 ∨ (M.op (σ (M.op X1 (τ X0))) (M.op X0 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54610 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq54610
    | (have j0 := eq54610 X0 X1 X2
       grind)
    | exact resolve eq54610 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54610
  have eq103655 : ∀ X0 X1 X2 X3 : G, (M.op (σ (M.op X1 (τ X0))) (M.op X0 X2)) = X0 ∨ (M.op (σ (M.op X1 (τ X0))) (M.op X0 X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq150 (M.op X1 (τ X0)) X1
       have i₂ := eq54683 X0 X1 X2
       grind)
    | exact superpose eq54683 eq150
    | (have j1 := eq54683 X0 X1 X2
       grind)
    | exact resolve eq150 eq54683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq54683
  have eq104459 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (M.op (σ (M.op X0 (τ X1))) (M.op X1 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq103655 X1 X0 X2 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103655
  have eq104460 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 (τ X1))) (M.op X1 X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq104459 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104459
  have eq104495 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op X1 X0)) (M.op (σ X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104460 X1 (σ X0) X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq104460
    | exact resolve eq104460 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104638 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X1 (τ (σ X0)))) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq104460 X1 (σ X0) (σ X0)
       have i₂ := eq131 X0
       grind)
    | exact superpose eq131 eq104460
    | exact resolve eq104460 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq104946 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X1 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq104638 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq104638
    | exact resolve eq104638 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104638
  have eq105082 : ∀ X0 X1 X3 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (M.op (σ (M.op X0 X1)) X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq104495 (M.op X0 X1) (σ (M.op x (τ X0))) X3
       have i₂ := eq104460 x X0 X1
       grind)
    | exact superpose eq104460 eq104495
    | exact resolve eq104495 eq104460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104460 eq104495
  have eq108726 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq105082 X1 X0 (σ (M.op X0 X0))
       have i₂ := eq104946 X0 X1
       grind)
    | exact superpose eq104946 eq105082
    | exact resolve eq105082 eq104946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104946 eq105082
  have eq109942 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq108726 y x
       grind)
    | exact superpose eq108726 eq16
    | (have r₁ := eq16
       have r₂ := eq108726 y x
       grind)
    | exact resolve eq16 eq108726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108726
  have eq110378 : False := by grind
  exact eq110378

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pxy_pxy_pxx_pxy_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq27 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op (M.op X1 X2) (M.op X3 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X3 X0) X1 X2 (M.op X0 x)
       have i₂ := eq19 X3 X0 x
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) ≠ X0 ∨ (k (M.op X0 X0) X1) = X0 ∨ (M.op X0 X0) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op x x) X1
       have i₂ := eq19 x x x
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 (M.op X0 X0) X1
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq55 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq55 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq55 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq58 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq56 (σ X0)
       grind)
    | exact superpose eq56 eq15
    | exact resolve eq15 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq56 (τ X0)
       grind)
    | exact superpose eq56 eq18
    | exact resolve eq18 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq60 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq60
    | exact resolve eq60 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq58 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq63 X0
       have i₂ := eq56 X0
       grind)
    | exact superpose eq56 eq63
    | exact resolve eq63 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq63
  have eq88 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq94 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq88
    | (have j0 := eq88 X0 X1
       grind)
    | exact resolve eq88 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq249 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq94 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq94
    | exact resolve eq94 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq282 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq249 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq249
    | (have j0 := eq249 X0 X1
       grind)
    | exact resolve eq249 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq249
  have eq286 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq282 X0 X1
       have j1 := eq12 X0 (σ X1)
       grind)
    | (have r₁ := eq282 X1 (M.op (τ X1) (τ X1))
       have r₂ := eq12 (σ (M.op (τ X1) (τ X1))) X1
       grind)
    | (have r₁ := eq282 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq282 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq289 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq286 X0 X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq286
    | (have j0 := eq286 X0 X1
       grind)
    | exact resolve eq286 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq286
  have eq835 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq289 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq289
    | exact resolve eq289 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq846 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq289 (σ X0) X1
       grind)
    | exact superpose eq289 eq15
    | (have j1 := eq289 (σ X0) X1
       grind)
    | exact resolve eq15 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq857 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq846 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq846
    | (have j0 := eq846 X0 X1
       grind)
    | exact resolve eq846 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846
  have eq872 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (M.op X0 (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq835 (τ X1) X0
       grind)
    | exact superpose eq835 eq18
    | (have j1 := eq835 (τ X1) X0
       grind)
    | exact resolve eq18 eq835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq835
  have eq1249 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X1) ∨ (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq54 (M.op X0 X1) X1
       have i₂ := eq27 X1 X0 X1 X0
       grind)
    | exact superpose eq27 eq54
    | (have j0 := eq54 (M.op X0 X1) X1
       grind)
    | (have r₁ := eq54 (M.op x X0) X0
       have r₂ := eq27 X0 x X0 x
       grind)
    | exact resolve eq54 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1267 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq1249 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249
  have eq2023 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq872 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq872
    | exact resolve eq872 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq2088 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2023 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2023
    | (have j0 := eq2023 X0 X1
       grind)
    | exact resolve eq2023 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2023
  have eq6392 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq857 x y
       grind)
    | exact superpose eq857 eq16
    | (have j1 := eq857 x y
       grind)
    | exact resolve eq16 eq857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6456 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq857 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq857
  have eq6502 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq6392
       have i₂ := eq2088 y x
       grind)
    | exact superpose eq2088 eq6392
    | (have j1 := eq2088 y x
       grind)
    | (have r₁ := eq6392
       have r₂ := eq2088 y x
       grind)
    | exact resolve eq6392 eq2088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6392
  have eq6503 : (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq6502
  have eq6648 : ∀ X0 : G, y = (M.op (M.op x x) (M.op y X0)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq19 x y X0
       have i₂ := eq6503
       grind)
    | exact superpose eq6503 eq19
    | exact resolve eq19 eq6503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6503
  have eq6696 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k (M.op X0 X0) X1)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6456 (M.op x x) X1
       have i₂ := eq19 x x x
       grind)
    | exact superpose eq19 eq6456
    | exact resolve eq6456 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6456
  have eq20426 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X1) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have i₂ := eq1267 X0 X1
       grind)
    | exact superpose eq1267 eq12
    | (have j0 := eq12 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have j1 := eq1267 X0 X1
       grind)
    | (have r₁ := eq12 (M.op (M.op X0 X1) (M.op X0 X1)) X1
       have r₂ := eq1267 X0 X1
       grind)
    | exact resolve eq12 eq1267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1267
  have eq20489 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X1) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq20426 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20426
  have eq20499 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X1) ∨ (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20489 X0 X1
       have i₂ := eq27 X1 X0 X1 X0
       grind)
    | exact superpose eq27 eq20489
    | (have j0 := eq20489 X0 X1
       grind)
    | exact resolve eq20489 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq20489
  have eq20500 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op (M.op X0 X1) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq20499 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20499
  have eq20673 : ∀ X0 X2 : G, (k (M.op X0 X0) (M.op X0 X2)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq20500 (M.op X0 x) (M.op x x)
       have i₂ := eq19 X0 x x
       grind)
    | exact superpose eq19 eq20500
    | exact resolve eq20500 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21046 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq6696 X0 (M.op X0 X1)
       have i₂ := eq20673 X0 X1
       grind)
    | exact superpose eq20673 eq6696
    | (have j0 := eq6696 X0 (M.op X0 X1)
       grind)
    | exact resolve eq6696 eq20673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6696 eq20673
  have eq21084 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq21046 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21046
  have eq23822 : (σ (M.op x x)) = (M.op (σ (M.op (M.op x x) (M.op x x))) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq21084 (M.op x x) (M.op y x)
       have i₂ := eq6648 x
       grind)
    | exact superpose eq6648 eq21084
    | exact resolve eq21084 eq6648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6648 eq21084
  have eq24108 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq23822
       have i₂ := eq19 x x x
       grind)
    | (have i₁ := eq23822
       have i₂ := eq19 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq19 eq23822
    | exact resolve eq23822 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23822
  have eq24109 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by grind
  clear eq24108
  have eq24429 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq24109
       grind)
    | exact superpose eq24109 eq16
    | exact resolve eq16 eq24109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24474 : (σ (M.op x x)) = (k (M.op (σ (M.op x x)) (σ (M.op x x))) (σ y)) := by
    first
    | (have i₁ := eq20500 (σ x) (σ y)
       have i₂ := eq24109
       grind)
    | exact superpose eq24109 eq20500
    | exact resolve eq20500 eq24109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20500 eq24109
  have eq24483 : (σ (M.op x x)) = (k (σ (M.op (M.op x x) (M.op x x))) (σ y)) := by
    first
    | (have i₁ := eq24474
       have i₂ := eq65 (M.op x x)
       grind)
    | exact superpose eq65 eq24474
    | exact resolve eq24474 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq24474
  have eq24500 : (σ (M.op x x)) = (σ (k (M.op (M.op x x) (M.op x x)) y)) := by
    first
    | (have i₁ := eq24483
       have i₂ := eq15 (M.op (M.op x x) (M.op x x)) y
       grind)
    | exact superpose eq15 eq24483
    | exact resolve eq24483 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24483
  have eq24510 : (σ (k x y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq24500
       have i₂ := eq19 x x x
       grind)
    | (have i₁ := eq24500
       have i₂ := eq19 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq19 eq24500
    | exact resolve eq24500 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq24500
  have eq24774 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq2088 y x
       have i₂ := eq24510
       grind)
    | exact superpose eq24510 eq2088
    | (have j0 := eq2088 y x
       grind)
    | exact resolve eq2088 eq24510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2088 eq24510
  have eq24902 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq24774
       have r₂ := eq24429
       grind)
    | exact resolve eq24774 eq24429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24774
  have eq25169 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq24429
       have i₂ := eq24902
       grind)
    | exact superpose eq24902 eq24429
    | exact resolve eq24429 eq24902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24429 eq24902
  have eq25204 : False := by grind
  exact eq25204

/-- `Equation2164`: `x = ((y ◇ z) ◇ x) ◇ (x ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyy_pxx_pyy_pyx_Equation2164 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2164 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2164.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq62 : ∀ X0 X3 X4 : G, (M.op X0 X3) = (M.op X0 (M.op (M.op X0 X3) X4)) := by
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
  have eq255 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq255 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq255 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq255 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq265 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq256 (σ X0)
       grind)
    | exact superpose eq256 eq15
    | exact resolve eq15 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq256 (τ X0)
       grind)
    | exact superpose eq256 eq17
    | exact resolve eq17 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq273 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq272 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq272
    | exact resolve eq272 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq280 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq265 X0
       have i₂ := eq256 X0
       grind)
    | exact superpose eq256 eq265
    | exact resolve eq265 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq289 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq273 X0
       have i₂ := eq256 X0
       grind)
    | exact superpose eq256 eq273
    | exact resolve eq273 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256 eq273
  have eq307 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X1 (σ X0) (σ X0)
       have i₂ := eq280 X0
       grind)
    | exact superpose eq280 eq61
    | exact resolve eq61 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ X0) (σ X0) X1
       have i₂ := eq280 X0
       grind)
    | exact superpose eq280 eq61
    | exact resolve eq61 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq309 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ X0) (σ X0) x
       have i₂ := eq280 X0
       grind)
    | exact superpose eq280 eq62
    | exact resolve eq62 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq318 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq289 X0
       grind)
    | exact superpose eq289 eq10
    | exact resolve eq10 eq289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq289
  have eq351 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq352 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq375 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq352 X0 X1
       have i₂ := eq280 X1
       grind)
    | exact superpose eq280 eq352
    | (have j0 := eq352 X0 X1
       grind)
    | exact resolve eq352 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq384 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq375 X0 X1
       have i₂ := eq280 X0
       grind)
    | exact superpose eq280 eq375
    | (have j0 := eq375 X0 X1
       grind)
    | exact resolve eq375 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq420 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq384 x y
       grind)
    | exact superpose eq384 eq16
    | (have j1 := eq384 x y
       grind)
    | exact resolve eq16 eq384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq384 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq3075 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (τ (M.op X0 X0)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq351 X0 X1
       have i₂ := eq318 X0
       grind)
    | exact superpose eq318 eq351
    | (have j0 := eq351 X0 X1
       grind)
    | exact resolve eq351 eq318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318 eq351
  have eq3438 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3075 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3075
    | (have j0 := eq3075 (σ X0) X1
       grind)
    | exact resolve eq3075 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3075
  have eq3523 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (τ (M.op (σ X0) (σ X0))) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3438 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3438
    | (have j0 := eq3438 X0 X1
       grind)
    | exact resolve eq3438 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3438
  have eq3533 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3523 X0 X1
       have i₂ := eq280 X0
       grind)
    | exact superpose eq280 eq3523
    | (have j0 := eq3523 X0 X1
       grind)
    | exact resolve eq3523 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3523
  have eq3537 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3533 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq3533
    | (have j0 := eq3533 X0 X1
       grind)
    | exact resolve eq3533 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3533
  have eq4435 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq420
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq420
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq420 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq4438 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq4435
  have eq32002 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq4438
       grind)
    | exact superpose eq4438 eq10
    | exact resolve eq10 eq4438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4438
  have eq32241 : (M.op x x) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32002
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq32002
    | exact resolve eq32002 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32002
  have eq32242 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq32241
  have eq32255 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq32242
       grind)
    | exact superpose eq32242 eq16
    | exact resolve eq16 eq32242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32262 : (σ y) = (M.op (σ y) (σ (M.op y y))) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq307 y (σ x)
       have i₂ := eq32242
       grind)
    | exact superpose eq32242 eq307
    | exact resolve eq307 eq32242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq32265 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq32242
       grind)
    | exact superpose eq32242 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq32242
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq32242
       grind)
    | exact resolve eq12 eq32242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32267 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq61 (σ x) (σ y) X0
       have i₂ := eq32242
       grind)
    | exact superpose eq32242 eq61
    | exact resolve eq61 eq32242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32242
  have eq32286 : (k (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq32265
  have eq32299 : (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32286
       have i₂ := eq280 y
       grind)
    | exact superpose eq280 eq32286
    | exact resolve eq32286 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32286
  have eq32305 : (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32299
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq32299
    | exact resolve eq32299 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32299
  have eq32316 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3537 x y
       have i₂ := eq32305
       grind)
    | exact superpose eq32305 eq3537
    | (have j0 := eq3537 x y
       grind)
    | exact resolve eq3537 eq32305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3537 eq32305
  have eq32442 : (σ (M.op x y)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq32316
  have eq34799 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32267 (σ (M.op y y))
       have i₂ := eq32262
       grind)
    | exact superpose eq32262 eq32267
    | exact resolve eq32267 eq32262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32262 eq32267
  have eq34836 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq34799
  have eq34850 : (σ y) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq34836
       have i₂ := eq280 y
       grind)
    | exact superpose eq280 eq34836
    | exact resolve eq34836 eq280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34836
  have eq34862 : (σ (M.op x y)) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq32442
       have i₂ := eq34850
       grind)
    | exact superpose eq34850 eq32442
    | exact resolve eq32442 eq34850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32442 eq34850
  have eq35035 : (σ (M.op x y)) = (σ y) ∨ (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq34862
  have eq35159 : (M.op x x) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq35035
       have r₂ := eq32255
       grind)
    | exact resolve eq35035 eq32255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32255 eq35035
  have eq35183 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x x)) (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq308 y X0
       have i₂ := eq35159
       grind)
    | exact superpose eq35159 eq308
    | exact resolve eq308 eq35159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq35306 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op x x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq61 X0 y y
       have i₂ := eq35159
       grind)
    | exact superpose eq35159 eq61
    | exact resolve eq61 eq35159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35307 : ∀ X0 : G, y = (M.op (M.op x x) (M.op y X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq61 y y X0
       have i₂ := eq35159
       grind)
    | exact superpose eq35159 eq61
    | exact resolve eq61 eq35159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35329 : y = (M.op (M.op x x) (M.op x x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq35306 y
       have i₂ := eq35159
       grind)
    | exact superpose eq35159 eq35306
    | exact resolve eq35306 eq35159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35159 eq35306
  have eq35363 : y = (M.op (M.op x x) (M.op x x)) ∨ y = (M.op x y) := by grind
  clear eq35329
  have eq35369 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq35363
       have i₂ := eq61 x x x
       grind)
    | (have i₁ := eq35363
       have i₂ := eq61 x (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact superpose eq61 eq35363
    | exact resolve eq35363 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35363
  have eq35373 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq61 X0 x y
       have i₂ := eq35369
       grind)
    | exact superpose eq35369 eq61
    | exact resolve eq61 eq35369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35369
  have eq39442 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq62 x x (M.op y x)
       have i₂ := eq35307 x
       grind)
    | exact superpose eq35307 eq62
    | exact resolve eq62 eq35307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq35307
  have eq39513 : y ≠ (M.op x x) ∨ y = (M.op x y) := by grind
  have eq458620 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq309 x (M.op (σ y) x)
       have i₂ := eq35183 x
       grind)
    | exact superpose eq35183 eq309
    | exact resolve eq309 eq35183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309 eq35183
  have eq463106 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq458620
       grind)
    | exact superpose eq458620 eq16
    | exact resolve eq16 eq458620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458620
  have eq463270 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ y = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq463106
       have i₂ := eq39442
       grind)
    | exact superpose eq39442 eq463106
    | exact resolve eq463106 eq39442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39442 eq463106
  have eq463271 : y = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq463270
  have eq463272 : y = (M.op x y) := by
    first
    | (have r₁ := eq463271
       have r₂ := eq39513
       grind)
    | exact resolve eq463271 eq39513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39513 eq463271
  have eq463319 : y ≠ y ∨ (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq463272
       grind)
    | exact superpose eq463272 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq463272
       grind)
    | exact resolve eq12 eq463272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq463321 : ∀ X0 : G, y = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq61 x y X0
       have i₂ := eq463272
       grind)
    | exact superpose eq463272 eq61
    | exact resolve eq61 eq463272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq463340 : (k y x) = (M.op y y) := by grind
  clear eq463319
  have eq463447 : y = (M.op y y) := by
    first
    | (have i₁ := eq463321 (M.op y x)
       have i₂ := eq463321 x
       grind)
    | exact superpose eq463321 eq463321
    | exact resolve eq463321 eq463321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463321
  have eq464573 : y = (k y x) := by
    first
    | (have i₁ := eq463340
       have i₂ := eq463447
       grind)
    | exact superpose eq463447 eq463340
    | exact resolve eq463340 eq463447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463340
  have eq464924 : (σ y) ≠ (σ y) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq430 x y
       have i₂ := eq464573
       grind)
    | exact superpose eq464573 eq430
    | (have j0 := eq430 x y
       grind)
    | exact resolve eq430 eq464573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq464573
  have eq464975 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq464924
  have eq464997 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq464975
       have i₂ := eq463447
       grind)
    | exact superpose eq463447 eq464975
    | exact resolve eq464975 eq463447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464975
  have eq478427 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq464997
       grind)
    | exact superpose eq464997 eq16
    | exact resolve eq16 eq464997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464997
  have eq478520 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq478427
       have i₂ := eq463272
       grind)
    | exact superpose eq463272 eq478427
    | exact resolve eq478427 eq463272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463272 eq478427
  have eq478521 : (σ y) = (σ (M.op x x)) := by grind
  clear eq478520
  have eq478598 : (M.op x x) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq478521
       grind)
    | exact superpose eq478521 eq10
    | exact resolve eq10 eq478521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478521
  have eq479307 : y = (M.op x x) := by
    first
    | (have i₁ := eq478598
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq478598
    | exact resolve eq478598 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478598
  have eq479354 : x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq35373 x
       have i₂ := eq479307
       grind)
    | exact superpose eq479307 eq35373
    | exact resolve eq35373 eq479307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35373 eq479307
  have eq479514 : x = y ∨ x = y := by
    first
    | (have i₁ := eq479354
       have i₂ := eq463447
       grind)
    | exact superpose eq463447 eq479354
    | exact resolve eq479354 eq463447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463447 eq479354
  have eq479515 : x = y := by grind
  clear eq479514
  have eq479519 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq479515
       grind)
    | exact superpose eq479515 eq16
    | exact resolve eq16 eq479515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479515
  have eq479563 : False := by grind
  exact eq479563
