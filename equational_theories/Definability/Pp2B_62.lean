import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4111`: `x ◇ x = ((y ◇ z) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then Y else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_y_pyy_pyx_Equation4111 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4111 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4111.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X2) X3) := by
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
  have eq177 : ∀ X0 X1 X4 X5 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X0) X4) X5) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq16 X1 (M.op (M.op x x) x) X4 X5
       have i₂ := eq16 X0 x x X4
       grind)
    | (have i₁ := eq16 X0 X0 X0 x
       have i₂ := eq16 X0 X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x y X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 x y X1
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X4 : G, (M.op X1 X1) = (M.op (M.op X0 X0) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 X1 (M.op x x) x X4
       have i₂ := eq16 X0 x x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 x x x
       have i₂ := eq16 X1 x x x
       grind)
    | (have i₁ := eq16 X0 X1 x (M.op (M.op X1 x) x)
       have i₂ := eq16 (M.op (M.op X1 x) x) X1 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (k X2 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq181 X1 X0
       grind)
    | (have i₁ := eq13 X2 X1
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq13
    | (have j0 := eq13 X2 X1
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq181 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq181 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq179 x X2
       have i₂ := eq179 x X0
       grind)
    | (have i₁ := eq179 (M.op (M.op (σ x) (σ y)) (σ y)) x
       have i₂ := eq179 X0 (M.op (M.op (σ x) (σ y)) (σ y))
       grind)
    | exact superpose eq179 eq179
    | exact resolve eq179 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 X3 X4 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X3 X3) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq180 X3 x X4
       have i₂ := eq180 X0 x X1
       grind)
    | (have i₁ := eq180 X0 (M.op X0 X0) X4
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq180
    | exact resolve eq180 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op X3 X4) X4) X5) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq16 x X3 X4 X5
       have i₂ := eq180 X0 x X1
       grind)
    | (have i₁ := eq16 (M.op X0 X0) X1 x X3
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X3) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq179 x X3
       have i₂ := eq180 X0 x X1
       grind)
    | (have i₁ := eq179 (M.op X0 X0) X1
       have i₂ := eq180 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq180 eq179
    | exact resolve eq179 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq180
  have eq474 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq511 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq198 X0 (M.op X1 X1) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq522 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (M.op X0 X0)
       have i₂ := eq511 (τ X1) X0
       grind)
    | exact superpose eq511 eq34
    | exact resolve eq34 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq580 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (k X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq474 X1 (M.op X0 X0)
       have i₂ := eq511 (σ X1) X0
       grind)
    | exact superpose eq511 eq474
    | exact resolve eq474 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq511
  have eq1419 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq181 X0 X1
       grind)
    | (have i₁ := eq11 X1 X1
       have i₂ := eq181 X0 X1
       grind)
    | exact superpose eq181 eq11
    | exact resolve eq11 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1441 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1442 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1524 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1419 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1419
  have eq2146 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq522 X1 (σ (M.op X1 X1))
       have i₂ := eq1524 X0 (σ (M.op X1 X1))
       grind)
    | exact superpose eq1524 eq522
    | (have j1 := eq1524 X0 (σ (M.op X1 X1))
       grind)
    | exact resolve eq522 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522
  have eq2148 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq580 X1 (τ (M.op X1 X1))
       have i₂ := eq1524 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq1524 eq580
    | (have j1 := eq1524 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq580 eq1524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2153 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1524 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1524
  have eq2154 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2148 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2148
  have eq2155 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2146 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2146
  have eq2209 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2154 X1 x
       have i₂ := eq2154 x X0
       grind)
    | exact superpose eq2154 eq2154
    | exact resolve eq2154 eq2154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2232 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) X3) X4) = (τ (M.op X0 X0)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq16 x X2 X3 X4
       have i₂ := eq2154 x X0
       grind)
    | exact superpose eq2154 eq16
    | exact resolve eq16 eq2154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2248 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) = (M.op (τ (M.op X0 X0)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq279 x X3 X1
       have i₂ := eq2154 x X0
       grind)
    | exact superpose eq2154 eq279
    | exact resolve eq279 eq2154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq2263 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op (τ (M.op X0 X0)) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 X2 X2 X3
       have i₂ := eq2154 X2 X0
       grind)
    | exact superpose eq2154 eq16
    | exact resolve eq16 eq2154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2321 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq2155 x X2
       have i₂ := eq2155 x X0
       grind)
    | exact superpose eq2155 eq2155
    | exact resolve eq2155 eq2155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2354 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2155 X1 x
       have i₂ := eq2155 x X0
       grind)
    | exact superpose eq2155 eq2155
    | exact resolve eq2155 eq2155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2371 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2155 X2 (M.op x x)
       have i₂ := eq249 x (M.op x x) X0 X1
       grind)
    | (have i₁ := eq2155 X2 (M.op x x)
       have i₂ := eq249 X0 X1 x (M.op x x)
       grind)
    | exact superpose eq249 eq2155
    | exact resolve eq2155 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2379 : ∀ X0 X2 X3 X4 : G, (σ (M.op X0 X0)) = (M.op (M.op (M.op X2 X2) X3) X4) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq177 X2 x X3 X4
       have i₂ := eq2155 x X0
       grind)
    | exact superpose eq2155 eq177
    | exact resolve eq177 eq2155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq2793 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2321 X1 x
       have i₂ := eq2155 x X0
       grind)
    | exact superpose eq2155 eq2321
    | exact resolve eq2321 eq2155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2155 eq2321
  have eq2964 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (σ (σ (M.op (M.op X0 X0) X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2354 (M.op x x) X2
       have i₂ := eq249 x (M.op x x) X0 X1
       grind)
    | (have i₁ := eq2354 (M.op x x) X2
       have i₂ := eq249 X0 X1 x (M.op x x)
       grind)
    | exact superpose eq249 eq2354
    | exact resolve eq2354 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq3002 : ∀ X0 X2 : G, (σ (σ (M.op X0 X0))) = (τ (M.op X2 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq2154 x X2
       have i₂ := eq2354 X0 x
       grind)
    | exact superpose eq2354 eq2154
    | exact resolve eq2154 eq2354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4591 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq1441
       grind)
    | exact superpose eq1441 eq39
    | exact resolve eq39 eq1441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1441
  have eq4592 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq4591
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4591
    | exact resolve eq4591 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4591
  have eq4594 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq4592
    | exact resolve eq4592 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4592
  have eq5221 : ∀ X0 X1 X3 : G, (σ (M.op (M.op X0 X0) X1)) = (τ (τ (M.op X3 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2209 X3 x
       have i₂ := eq2371 X0 X1 x
       grind)
    | exact superpose eq2371 eq2209
    | exact resolve eq2209 eq2371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2209 eq2371
  have eq7116 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (σ (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq2793 x X1
       have i₂ := eq2354 X0 x
       grind)
    | exact superpose eq2354 eq2793
    | exact resolve eq2793 eq2354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2793
  have eq7288 : ∀ X0 X2 : G, (τ (M.op X2 X2)) = (σ (σ (σ (σ (M.op X0 X0))))) := by
    intro X0 X2
    first
    | (have i₁ := eq3002 x X2
       have i₂ := eq2354 X0 x
       grind)
    | exact superpose eq2354 eq3002
    | exact resolve eq3002 eq2354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2354 eq3002
  have eq155254 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4594 eq1442
    | exact resolve eq1442 eq4594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442 eq4594
  have eq155265 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq155254
       have r₂ := eq27
       grind)
    | exact resolve eq155254 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155254
  have eq155297 : ∀ X0 : G, (τ (σ x)) = (k X0 (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq155265 eq580
    | exact resolve eq580 eq155265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580 eq155265
  have eq155650 : ∀ X0 : G, x = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq29 eq155297
    | exact resolve eq155297 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155297
  have eq155766 : ∀ X0 : G, x = (k X0 x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq155650 X0
       have j1 := eq13 X0 x
       grind)
    | (have r₁ := eq155650 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq155650 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155650
  have eq155856 : ∀ X0 : G, x ≠ x ∨ (M.op X0 X0) = x ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2153 X0 x
       have i₂ := eq155766 x
       grind)
    | exact superpose eq155766 eq2153
    | (have j0 := eq2153 X0 x
       grind)
    | (have r₁ := eq2153 X0 x
       have r₂ := eq155766 x
       grind)
    | exact resolve eq2153 eq155766
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153 eq155766
  have eq155876 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq155856 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155856
  have eq156731 : ∀ X0 X2 : G, (M.op X0 X0) = (M.op x X2) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0 X2
    first
    | (have i₁ := eq2263 x X0 (τ (M.op x x)) X2
       have i₂ := eq155876 (τ (M.op x x))
       grind)
    | exact superpose eq155876 eq2263
    | exact resolve eq2263 eq155876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2263
  have eq156775 : ∀ X2 : G, x = (M.op x X2) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X2
    first
    | exact superpose eq155876 eq156731
    | exact resolve eq156731 eq155876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155876 eq156731
  have eq161445 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq156775 y
       grind)
    | exact superpose eq156775 eq18
    | (have j1 := eq156775 y
       grind)
    | exact resolve eq18 eq156775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156775
  have eq161661 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq161445
  have eq161839 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq161661 eq222
    | exact resolve eq222 eq161661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq161942 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) (σ y)) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq26 eq161839
    | (have j0 := eq161839 X1 X0
       grind)
    | exact resolve eq161839 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161839
  have eq161994 : ∀ X0 X1 : G, (M.op (σ x) X1) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq161661 eq161942
    | exact resolve eq161942 eq161661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161942
  have eq162235 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq161994 eq26
    | (have j1 := eq161994 X0 (σ y)
       grind)
    | exact resolve eq26 eq161994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq162279 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) = (M.op (τ (M.op (σ x) X0)) X2) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq161994 eq2248
    | exact resolve eq2248 eq161994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2248 eq161994
  have eq162473 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (τ (M.op (σ x) X0)) X2) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq161661 eq162279
    | exact resolve eq162279 eq161661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162279
  have eq162476 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq161661 eq162235
    | exact resolve eq162235 eq161661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162235
  have eq162501 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) X1) = (M.op (τ (M.op (σ x) X0)) X2) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq26 eq162473
    | (have j0 := eq162473 X0 X1 X2
       grind)
    | exact resolve eq162473 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162473
  have eq162521 : ∀ X0 X1 X2 : G, (M.op (σ x) X1) = (M.op (τ (M.op (σ x) X0)) X2) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq161661 eq162501
    | exact resolve eq162501 eq161661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161661 eq162501
  have eq162541 : ∀ X1 X2 : G, (M.op (σ x) X1) = (M.op (τ (σ x)) X2) ∨ x = (M.op x y) := by
    intro X1 X2
    first
    | exact superpose eq162476 eq162521
    | exact resolve eq162521 eq162476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162521
  have eq162557 : ∀ X1 X2 : G, (M.op (σ x) X1) = (M.op x X2) ∨ x = (M.op x y) := by
    intro X1 X2
    first
    | exact superpose eq29 eq162541
    | exact resolve eq162541 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162541
  have eq162565 : ∀ X2 : G, (σ x) = (M.op x X2) ∨ x = (M.op x y) := by
    intro X2
    first
    | exact superpose eq162476 eq162557
    | exact resolve eq162557 eq162476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162557
  have eq162585 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq162476 eq181
    | exact resolve eq181 eq162476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq162612 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq162476 eq2154
    | exact resolve eq2154 eq162476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2154 eq162476
  have eq162895 : ∀ X0 : G, (M.op X0 X0) = x ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq162612
    | exact resolve eq162612 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq162612
  have eq162972 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq162585 eq162895
    | exact resolve eq162895 eq162585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162585 eq162895
  have eq163052 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq162972
  have eq163131 : (M.op x y) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq162565 y
       grind)
    | (have i₁ := eq18
       have i₂ := eq162565 x
       grind)
    | exact superpose eq162565 eq18
    | (have j1 := eq162565 y
       grind)
    | exact resolve eq18 eq162565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162565
  have eq163454 : x = (M.op x y) := by
    first
    | (have r₁ := eq163131
       have r₂ := eq163052
       grind)
    | exact resolve eq163131 eq163052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163052 eq163131
  have eq163531 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq163454
       grind)
    | exact superpose eq163454 eq18
    | exact resolve eq18 eq163454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq163532 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq163454
       grind)
    | exact superpose eq163454 eq22
    | exact resolve eq22 eq163454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq163454
  have eq163542 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq163532 eq20
    | exact resolve eq20 eq163532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163532
  have eq163617 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | exact superpose eq163531 eq178
    | exact resolve eq178 eq163531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq164050 : ∀ X0 X1 X3 X4 : G, (σ (M.op X1 X1)) = (M.op (M.op (M.op (M.op x y) X0) X3) X4) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq2379 X1 x X3 X4
       have i₂ := eq163617 x X0
       grind)
    | (have i₁ := eq2379 X0 (M.op x y) X3 X4
       have i₂ := eq163617 X0 (M.op x y)
       grind)
    | exact superpose eq163617 eq2379
    | exact resolve eq2379 eq163617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2379
  have eq164121 : ∀ X0 X1 X3 : G, (M.op X1 X1) = (σ (σ (M.op (M.op (M.op x y) X0) X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2964 x X3 X1
       have i₂ := eq163617 x X0
       grind)
    | (have i₁ := eq2964 (M.op x y) X1 x
       have i₂ := eq163617 X0 (M.op x y)
       grind)
    | exact superpose eq163617 eq2964
    | exact resolve eq2964 eq163617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2964
  have eq164243 : ∀ X0 X2 X3 : G, (τ (τ (M.op X3 X3))) = (σ (M.op (M.op (M.op x y) X0) X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq5221 x X2 X3
       have i₂ := eq163617 x X0
       grind)
    | (have i₁ := eq5221 (M.op x y) x X3
       have i₂ := eq163617 X0 (M.op x y)
       grind)
    | exact superpose eq163617 eq5221
    | exact resolve eq5221 eq163617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5221
  have eq164301 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (σ (σ (σ (M.op (M.op x y) X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq7116 x X1
       have i₂ := eq163617 x X0
       grind)
    | (have i₁ := eq7116 (M.op x y) X1
       have i₂ := eq163617 X0 (M.op x y)
       grind)
    | exact superpose eq163617 eq7116
    | exact resolve eq7116 eq163617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7116
  have eq164309 : ∀ X0 X1 : G, (τ (M.op X1 X1)) = (σ (σ (σ (σ (M.op (M.op x y) X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq7288 x X1
       have i₂ := eq163617 x X0
       grind)
    | (have i₁ := eq7288 (M.op x y) x
       have i₂ := eq163617 X0 (M.op x y)
       grind)
    | exact superpose eq163617 eq7288
    | exact resolve eq7288 eq163617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7288
  have eq164343 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X3) X4) = (M.op (M.op (M.op (M.op x y) X0) X1) X2) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq277 X3 X4 X1 X1 X2
       have i₂ := eq163617 X1 X0
       grind)
    | (have i₁ := eq277 X0 X1 (M.op x y) X1 x
       have i₂ := eq163617 X0 X1
       grind)
    | exact superpose eq163617 eq277
    | exact resolve eq277 eq163617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq164351 : ∀ X0 X1 X2 X3 : G, (τ (M.op X3 X3)) = (M.op (M.op (M.op (M.op x y) X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2232 X3 X1 X1 X2
       have i₂ := eq163617 X1 X0
       grind)
    | (have i₁ := eq2232 X0 (M.op x y) X1 x
       have i₂ := eq163617 X0 X1
       grind)
    | exact superpose eq163617 eq2232
    | exact resolve eq2232 eq163617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2232
  have eq164677 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | exact superpose eq163617 eq163531
    | exact resolve eq163531 eq163617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163531 eq163617
  have eq164923 : ∀ X0 X1 X2 : G, (τ (M.op x y)) = (M.op (M.op (M.op (M.op x y) X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq164351 X0 X1 X2 x
       have i₂ := eq164677 x
       grind)
    | exact superpose eq164677 eq164351
    | exact resolve eq164351 eq164677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164351
  have eq164926 : ∀ X0 X1 X2 X4 : G, (M.op (M.op x y) X4) = (M.op (M.op (M.op (M.op x y) X0) X1) X2) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq164343 X0 X1 X2 x X4
       have i₂ := eq164677 x
       grind)
    | exact superpose eq164677 eq164343
    | exact resolve eq164343 eq164677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164343
  have eq164951 : ∀ X0 : G, (τ (M.op x y)) = (σ (σ (σ (σ (M.op (M.op x y) X0))))) := by
    intro X0
    first
    | (have i₁ := eq164309 X0 x
       have i₂ := eq164677 x
       grind)
    | exact superpose eq164677 eq164309
    | exact resolve eq164309 eq164677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164309
  have eq164959 : ∀ X0 : G, (σ (M.op x y)) = (σ (σ (σ (σ (M.op (M.op x y) X0))))) := by
    intro X0
    first
    | (have i₁ := eq164301 X0 x
       have i₂ := eq164677 x
       grind)
    | exact superpose eq164677 eq164301
    | exact resolve eq164301 eq164677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164301
  have eq165015 : ∀ X0 X2 : G, (σ (M.op (M.op (M.op x y) X0) X2)) = (τ (τ (M.op x y))) := by
    intro X0 X2
    first
    | (have i₁ := eq164243 X0 X2 x
       have i₂ := eq164677 x
       grind)
    | exact superpose eq164677 eq164243
    | exact resolve eq164243 eq164677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164243
  have eq165113 : ∀ X0 X3 : G, (M.op x y) = (σ (σ (M.op (M.op (M.op x y) X0) X3))) := by
    intro X0 X3
    first
    | (have i₁ := eq164121 X0 x X3
       have i₂ := eq164677 x
       grind)
    | exact superpose eq164677 eq164121
    | exact resolve eq164121 eq164677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164121
  have eq165160 : ∀ X0 X3 X4 : G, (σ (M.op x y)) = (M.op (M.op (M.op (M.op x y) X0) X3) X4) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq164050 X0 x X3 X4
       have i₂ := eq164677 x
       grind)
    | exact superpose eq164677 eq164050
    | exact resolve eq164050 eq164677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164050 eq164677
  have eq165270 : ∀ X4 : G, (τ (M.op x y)) = (M.op (M.op x y) X4) := by
    intro X4
    first
    | exact superpose eq164923 eq164926
    | exact resolve eq164926 eq164923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164926
  have eq165291 : (σ (M.op x y)) = (τ (M.op x y)) := by
    first
    | exact superpose eq164951 eq164959
    | exact resolve eq164959 eq164951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164951 eq164959
  have eq165426 : (M.op x y) = (σ (τ (τ (M.op x y)))) := by
    first
    | exact superpose eq165015 eq165113
    | exact resolve eq165113 eq165015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165015 eq165113
  have eq165464 : (σ (M.op x y)) = (τ (M.op x y)) := by
    first
    | exact superpose eq164923 eq165160
    | exact resolve eq165160 eq164923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164923 eq165160
  have eq165523 : (σ (M.op x y)) = (τ (M.op x y)) := by
    first
    | exact superpose eq20 eq165291
    | exact resolve eq165291 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165291
  have eq165650 : (M.op x y) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq165426
       have i₂ := eq14 (τ sF0)
       grind)
    | exact superpose eq14 eq165426
    | exact resolve eq165426 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165426
  have eq165675 : (σ (M.op x y)) = (τ (M.op x y)) := by
    first
    | exact superpose eq20 eq165464
    | exact resolve eq165464 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq165464
  have eq165713 : (σ x) = (τ (M.op x y)) := by
    first
    | exact superpose eq163542 eq165523
    | exact resolve eq165523 eq163542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163542 eq165523
  have eq165822 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq165650 eq165675
    | exact resolve eq165675 eq165650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165675
  have eq165846 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq165650 eq165713
    | exact resolve eq165713 eq165650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165713
  have eq166163 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq165846 eq26
    | exact resolve eq26 eq165846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq165846
  have eq166207 : (M.op (σ x) (σ y)) = (τ (M.op x y)) := by
    first
    | exact superpose eq165270 eq166163
    | exact resolve eq166163 eq165270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165270 eq166163
  have eq166215 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq165650 eq166207
    | exact resolve eq166207 eq165650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165650 eq166207
  have eq166220 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq166215 eq27
    | exact resolve eq27 eq166215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq166215
  have eq166321 : False := by grind
  exact eq166321

/-- `Equation4111`: `x ◇ x = ((y ◇ z) ◇ z) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pyy_Equation4111 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) Law4111 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4111.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X2) X3) := by
    intro X0 X1 X2 X3
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x x x
       have i₂ := eq9 X1 x x x
       grind)
    | (have i₁ := eq9 X0 X1 x (M.op (M.op X1 x) x)
       have i₂ := eq9 (M.op (M.op X1 x) x) X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq29 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq29 X0 X1
       grind)
    | exact resolve eq13 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq31 (σ X1) (σ X0)
       grind)
    | exact superpose eq31 eq15
    | (have j1 := eq31 (M.op (σ X0) (σ X1)) (σ (k X1 X0))
       grind)
    | exact resolve eq15 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq29
    | exact resolve eq29 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq29
  have eq325 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq33
    | (have j0 := eq33 X0 X1
       have j1 := eq31 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq33 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq33
  have eq5089 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq325 x y
       grind)
    | exact superpose eq325 eq16
    | (have j1 := eq325 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq325 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq325 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq325 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325
  have eq5106 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq5089
  have eq8301 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq5106
       grind)
    | exact superpose eq5106 eq10
    | exact resolve eq10 eq5106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5106
  have eq8319 : x = y ∨ x = y := by
    first
    | (have i₁ := eq8301
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8301
    | exact resolve eq8301 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8301
  have eq8320 : x = y := by grind
  clear eq8319
  have eq15626 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8320
       grind)
    | exact superpose eq8320 eq16
    | exact resolve eq16 eq8320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8320
  have eq15627 : False := by grind
  exact eq15627

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxy_pxx_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X0 X0) := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq63 (σ X0)
       grind)
    | exact superpose eq63 eq15
    | exact resolve eq15 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq66
    | exact resolve eq66 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq66
  have eq93 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq396 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq419 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq396 X0 X1
       have i₂ := eq77 X0
       grind)
    | exact superpose eq77 eq396
    | (have j0 := eq396 X0 X1
       grind)
    | exact resolve eq396 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq942 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq419 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq419
    | exact resolve eq419 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq960 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq942 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq942
    | (have j0 := eq942 X0 X1
       grind)
    | exact resolve eq942 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq972 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq960 X0 X1
       have j1 := eq93 X1 X0
       grind)
    | (have r₁ := eq960 X1 X0
       have r₂ := eq93 X0 X1
       grind)
    | (have r₁ := eq960 (M.op X1 (σ X0)) (M.op X0 X0)
       have r₂ := eq93 X0 X1
       grind)
    | exact resolve eq960 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq960
  have eq975 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq972 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq972
    | exact resolve eq972 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq988 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq972 (σ X1) X0
       grind)
    | exact superpose eq972 eq15
    | (have j1 := eq972 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq1030 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq975 X0 (τ X1)
       grind)
    | exact superpose eq975 eq19
    | (have j1 := eq975 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq975
  have eq1202 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1030 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1030
    | exact resolve eq1030 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1030
  have eq1244 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1202 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1202
    | (have j0 := eq1202 (σ (k X1 X0)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq1202 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1202
  have eq1388 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq988 x y
       grind)
    | exact superpose eq988 eq16
    | (have j1 := eq988 x y
       grind)
    | exact resolve eq16 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq1403 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1388
       have i₂ := eq1244 y x
       grind)
    | exact superpose eq1244 eq1388
    | (have j1 := eq1244 (σ x) (σ y)
       grind)
    | (have r₁ := eq1388
       have r₂ := eq1244 y x
       grind)
    | (have r₁ := eq1388
       have r₂ := eq1244 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1388
       have r₂ := eq1244 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1388 eq1244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244 eq1388
  have eq1404 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1403
  have eq1407 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1404
       grind)
    | exact superpose eq1404 eq16
    | exact resolve eq16 eq1404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1404
  have eq1408 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1407
       have r₂ := eq77 x
       grind)
    | exact resolve eq1407 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1407
  have eq1409 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1408
       grind)
    | exact superpose eq1408 eq16
    | exact resolve eq16 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1410 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1408
       grind)
    | exact superpose eq1408 eq10
    | exact resolve eq10 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408
  have eq1454 : x = y := by
    first
    | (have i₁ := eq1410
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1410
    | exact resolve eq1410 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1410
  have eq1455 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1409
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq1409
    | exact resolve eq1409 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq1409
  have eq1456 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1455
       have i₂ := eq1454
       grind)
    | exact superpose eq1454 eq1455
    | exact resolve eq1455 eq1454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1454 eq1455
  have eq1457 : False := by grind
  exact eq1457

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_y_pyx_x_pyx_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq427 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X1 X0
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq441 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq436 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq436 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq436 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq436 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq450 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq427 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq427 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq427 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq427 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq555 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq450 X0 X1
       grind)
    | exact superpose eq450 eq9
    | (have j1 := eq450 X0 X1
       grind)
    | exact resolve eq9 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq560 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq555 X0 X1
       have j1 := eq441 X1 X0
       grind)
    | (have r₁ := eq555 X1 X1
       have r₂ := eq441 X0 X1
       grind)
    | exact resolve eq555 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441 eq555
  have eq577 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq560 (σ X0) (σ X1)
       grind)
    | exact superpose eq560 eq15
    | exact resolve eq15 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq577 X0 X1
       have i₂ := eq560 X0 X1
       grind)
    | exact superpose eq560 eq577
    | exact resolve eq577 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560 eq577
  have eq822 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq604 x y
       grind)
    | exact superpose eq604 eq16
    | (have r₁ := eq16
       have r₂ := eq604 x y
       grind)
    | exact resolve eq16 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq838 : False := by grind
  exact eq838

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pxy_pxx_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq65 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq90 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq92 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq349 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq9
    | (have j1 := eq65 X0
       grind)
    | exact resolve eq9 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq352 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq349 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq349 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq349 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq363 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq352 (σ X0)
       grind)
    | exact superpose eq352 eq15
    | exact resolve eq15 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq363 X0
       have i₂ := eq352 X0
       grind)
    | exact superpose eq352 eq363
    | exact resolve eq363 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq363
  have eq723 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq90 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq742 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (τ X1) X0) = X0 ∨ (τ X1) = X0 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq12
    | (have j1 := eq92 X1 X0
       grind)
    | (have r₁ := eq12 (τ X0) X1
       have r₂ := eq92 X0 X1
       grind)
    | (have r₁ := eq12 X0 (τ X0)
       have r₂ := eq92 X0 (M.op X0 (τ X0))
       grind)
    | exact resolve eq12 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq753 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 ∨ (k (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq742 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742
  have eq2592 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq753 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq753
    | exact resolve eq753 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq2647 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2592 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2592
    | (have j0 := eq2592 X0 X1
       grind)
    | exact resolve eq2592 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2592
  have eq2691 : ∀ X0 X1 : G, (k X0 X1) = (τ (σ (M.op X0 X1))) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq2647 X0 X1
       grind)
    | exact superpose eq2647 eq10
    | (have j1 := eq2647 X0 X1
       grind)
    | exact resolve eq10 eq2647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2736 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2691 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq2691
    | (have j0 := eq2691 X0 X1
       grind)
    | exact resolve eq2691 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2691
  have eq2777 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (σ X0) = X1 ∨ (k X0 (τ X1)) = (τ (M.op (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq29 X0 X1
       have i₂ := eq2736 (σ X0) X1
       grind)
    | exact superpose eq2736 eq29
    | (have j1 := eq2736 (σ X0) X1
       grind)
    | exact resolve eq29 eq2736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2736
  have eq4800 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X1) X0
       have i₂ := eq2777 X1 (σ X0)
       grind)
    | exact superpose eq2777 eq23
    | (have j1 := eq2777 X0 (σ X1)
       grind)
    | exact resolve eq23 eq2777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2777
  have eq4861 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4800 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4800
    | (have j0 := eq4800 X0 X1
       grind)
    | exact resolve eq4800 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4800
  have eq4895 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (σ X0) = (σ X1) ∨ (k X1 (τ (σ X0))) = (τ (M.op (σ X1) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4861 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4861
    | (have j0 := eq4861 X0 X1
       grind)
    | exact resolve eq4861 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4861
  have eq4904 : ∀ X0 X1 : G, (k X1 X0) = (τ (M.op (σ X1) (σ X0))) ∨ (k X1 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4895 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4895
    | (have j0 := eq4895 X0 X1
       grind)
    | exact resolve eq4895 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4895
  have eq5102 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (k X0 X1) = X1 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op (σ X0) (σ X1))
       have i₂ := eq4904 X1 X0
       grind)
    | exact superpose eq4904 eq11
    | (have j1 := eq4904 X1 X0
       grind)
    | exact resolve eq11 eq4904
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4904
  have eq5961 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5102 x y
       grind)
    | exact superpose eq5102 eq16
    | (have j1 := eq5102 x y
       grind)
    | exact resolve eq16 eq5102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5102
  have eq5982 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq5961
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq5961
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq5961
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5961
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5961 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5983 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (k x y) := by
    first
    | (have i₁ := eq5961
       have i₂ := eq2647 x y
       grind)
    | exact superpose eq2647 eq5961
    | (have j1 := eq2647 x y
       grind)
    | (have r₁ := eq5961
       have r₂ := eq2647 x y
       grind)
    | (have r₁ := eq5961
       have r₂ := eq2647 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq5961
       have r₂ := eq2647 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq5961 eq2647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2647 eq5961
  have eq5986 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5983
  have eq5987 : x = y ∨ (σ x) = (σ y) ∨ y = (k x y) := by grind
  clear eq5986
  have eq5988 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq5982
  have eq5989 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq5988
  have eq5993 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5987
       grind)
    | exact superpose eq5987 eq16
    | exact resolve eq16 eq5987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5987
  have eq5994 : y = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq5993
       have r₂ := eq382 x
       grind)
    | exact resolve eq5993 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5993
  have eq5998 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq723 x y
       have i₂ := eq5994
       grind)
    | exact superpose eq5994 eq723
    | (have j0 := eq723 x y
       grind)
    | exact resolve eq723 eq5994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723 eq5994
  have eq6005 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5998
  have eq6006 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq6005
  have eq6010 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5989
       grind)
    | exact superpose eq5989 eq16
    | exact resolve eq16 eq5989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5989
  have eq6011 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6010
       have r₂ := eq382 x
       grind)
    | exact resolve eq6010 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6010
  have eq6023 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6006
       grind)
    | exact superpose eq6006 eq16
    | exact resolve eq16 eq6006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6006
  have eq6050 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6023
       have i₂ := eq6011
       grind)
    | exact superpose eq6011 eq6023
    | exact resolve eq6023 eq6011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6011 eq6023
  have eq6051 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq6050
  have eq6052 : (σ x) = (σ y) := by grind
  clear eq6051
  have eq6053 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6052
       grind)
    | exact superpose eq6052 eq16
    | exact resolve eq16 eq6052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6054 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6052
       grind)
    | exact superpose eq6052 eq10
    | exact resolve eq10 eq6052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6052
  have eq6109 : x = y := by
    first
    | (have i₁ := eq6054
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6054
    | exact resolve eq6054 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6054
  have eq6110 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6053
       have i₂ := eq382 x
       grind)
    | exact superpose eq382 eq6053
    | exact resolve eq6053 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq6053
  have eq6113 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6110
       have i₂ := eq6109
       grind)
    | exact superpose eq6109 eq6110
    | exact resolve eq6110 eq6109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6109 eq6110
  have eq6114 : False := by grind
  exact eq6114

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pxy_pxy_pxx_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op X0 (M.op X1 X0)))) = X0 := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq28 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
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
  have eq35 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq33 (σ X0)
       grind)
    | exact superpose eq33 eq15
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
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
  have eq38 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq35
    | exact resolve eq35 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq38 X0
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq38
    | exact resolve eq38 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq76 : ∀ X0 X1 : G, (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq40 (k X1 (τ X0))
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq40
    | exact resolve eq40 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq91 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq91 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq91
    | (have j0 := eq91 X0 X1
       grind)
    | exact resolve eq91 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq91
  have eq170 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq93
    | exact resolve eq93 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq172 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op (k X0 (τ X1)) (k X0 (τ X1)))) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93 (k X1 (τ X0)) X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq200 : ∀ X0 X1 X2 : G, (M.op (k (σ X0) X1) (k (σ X0) X1)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq172 X0 X1 X2
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq172
    | (have j0 := eq172 X0 X1 X2
       grind)
    | exact resolve eq172 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq172
  have eq202 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq170 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq170
    | (have j0 := eq170 X0 X1
       grind)
    | exact resolve eq170 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq170
  have eq207 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq202 X0 X1
       have j1 := eq80 X1 X0
       grind)
    | (have r₁ := eq202 X1 X0
       have r₂ := eq80 X0 X1
       grind)
    | exact resolve eq202 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq212 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq207 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq207
    | (have j0 := eq207 X0 X1
       grind)
    | exact resolve eq207 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq207
  have eq475 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq212 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq212
    | exact resolve eq212 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq2002 : ∀ X0 X1 X2 X3 : G, (M.op (k (σ X0) X1) (σ X2)) ≠ (M.op (k (σ X0) X1) X3) ∨ (M.op (k (σ X0) X1) (σ X2)) = (k (k (σ X0) X1) X3) ∨ (M.op X3 X3) = (M.op X3 (k (σ X0) X1)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (k (σ X0) X1) X1
       have i₂ := eq200 X0 X1 X2
       grind)
    | exact superpose eq200 eq13
    | (have j0 := eq13 (k (σ X0) X1) X3
       have j1 := eq200 X0 X1 X2
       grind)
    | (have r₁ := eq13 (k (σ X0) X1) (σ X2)
       have r₂ := eq200 X0 X1 X2
       grind)
    | exact resolve eq13 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq103147 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (M.op (σ X2) (k (σ X0) X1)) = (M.op (σ X2) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2002 X0 X1 X2 (σ X2)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002
  have eq103162 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (M.op X2 X2)) = (M.op (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq103147 X0 X1 X2
       have j1 := eq12 (k (σ X0) X1) (σ X2)
       grind)
    | (have r₁ := eq103147 X0 X1 X2
       have r₂ := eq12 (k (σ X0) X1) (σ X2)
       grind)
    | exact resolve eq103147 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103147
  have eq103249 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) (σ X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq103162 X0 X1 X2
       have j1 := eq80 X2 (k (σ X0) X1)
       grind)
    | (have r₁ := eq103162 X0 X1 X0
       have r₂ := eq80 X0 (k (σ X0) X1)
       grind)
    | exact resolve eq103162 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq103162
  have eq103316 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) ∨ (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq103249 X0 X1 X2
       have i₂ := eq28 X0 X1 X2
       grind)
    | exact superpose eq28 eq103249
    | (have j0 := eq103249 X0 X1 X2
       grind)
    | exact resolve eq103249 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq103249
  have eq103317 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (M.op (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq103316 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103316
  have eq103631 : ∀ X0 X1 X2 : G, (k (σ (k X0 (τ X1))) X2) = (M.op (k (σ X0) X1) (σ (τ X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X2 (k X0 (τ X1))
       have i₂ := eq103317 X0 X1 (τ X2)
       grind)
    | exact superpose eq103317 eq18
    | exact resolve eq18 eq103317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103317
  have eq103888 : ∀ X0 X1 X2 : G, (k (σ (k X0 (τ X1))) X2) = (M.op (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq103631 X0 X1 X2
       have i₂ := eq11 X2
       grind)
    | exact superpose eq11 eq103631
    | exact resolve eq103631 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103631
  have eq104092 : ∀ X0 X1 X2 : G, (k (k (σ X0) X1) X2) = (M.op (k (σ X0) X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq103888 X0 X1 X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq103888
    | exact resolve eq103888 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq103888
  have eq104286 : ∀ X0 X1 X2 : G, (k (k X0 X1) X2) = (M.op (k X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104092 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq104092
    | exact resolve eq104092 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104092
  have eq109556 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq104286 X0 X0 x
       have i₂ := eq33 X0
       grind)
    | exact superpose eq33 eq104286
    | exact resolve eq104286 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq109557 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) X2) = (M.op (M.op X0 X1) X2) ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq104286 X1 X0 X2
       have i₂ := eq475 X0 X1
       grind)
    | exact superpose eq475 eq104286
    | (have j1 := eq475 X2 (M.op X0 X1)
       grind)
    | exact resolve eq104286 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475 eq104286
  have eq273095 : ∀ X0 X2 : G, (M.op X0 X0) = X0 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq109557 X0 (M.op X0 (M.op X0 (M.op x X0))) X2
       have i₂ := eq9 X0 x
       grind)
    | exact superpose eq9 eq109557
    | exact resolve eq109557 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109557
  have eq273846 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq109556 X0 X1
       have i₂ := eq273095 X0 X2
       grind)
    | exact superpose eq273095 eq109556
    | (have j1 := eq273095 X0 X1
       grind)
    | exact resolve eq109556 eq273095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109556 eq273095
  have eq276047 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq273846 X0 X1 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273846
  have eq276048 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq276047 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276047
  have eq276456 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq276048 (σ X0) (σ X1)
       grind)
    | exact superpose eq276048 eq15
    | exact resolve eq15 eq276048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276771 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq276456 X0 X1
       have i₂ := eq276048 X0 X1
       grind)
    | exact superpose eq276048 eq276456
    | exact resolve eq276456 eq276048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276048 eq276456
  have eq292149 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq276771 x y
       grind)
    | exact superpose eq276771 eq16
    | (have r₁ := eq16
       have r₂ := eq276771 x y
       grind)
    | exact resolve eq16 eq276771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276771
  have eq292328 : False := by grind
  exact eq292328

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyy_pxy_pyy_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq31 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
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
  have eq47 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq48 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq52 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq48 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq48 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq48 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq162 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq169 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq162 X0 X1
       have j1 := eq52 X1 X0
       grind)
    | (have r₁ := eq162 X0 X0
       have r₂ := eq52 X0 X0
       grind)
    | (have r₁ := eq162 X1 X0
       have r₂ := eq52 X0 X1
       grind)
    | exact resolve eq162 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq162
  have eq376 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq169 (σ X0) (σ X1)
       grind)
    | exact superpose eq169 eq15
    | exact resolve eq15 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq376 X0 X1
       have i₂ := eq169 X0 X1
       grind)
    | exact superpose eq169 eq376
    | exact resolve eq376 eq169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169 eq376
  have eq386 : False := by grind
  exact eq386

/-- `Equation413`: `x = x ◇ (x ◇ (x ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_x_pxy_x_pxy_Equation413 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law413 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law413.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq268 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq275 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq268 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq276 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq275 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq379 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq276 (σ x) (σ y)
       grind)
    | exact superpose eq276 eq16
    | (have j1 := eq276 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq276 X0 X1
       grind)
    | exact superpose eq276 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq276 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq276 X0 X1
       grind)
    | exact resolve eq13 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq382 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382
  have eq389 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq388 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq388 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq388 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq390 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq379
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq379
    | exact resolve eq379 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq404 : ∀ X0 X1 : G, (k X0 (τ X1)) = X0 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq389 X0 (τ X1)
       grind)
    | exact superpose eq389 eq18
    | (have j1 := eq389 X0 (τ X1)
       grind)
    | exact resolve eq18 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq421 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq389 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq910 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (τ X1))) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 (τ X1)
       have i₂ := eq404 (τ X0) X1
       grind)
    | exact superpose eq404 eq17
    | (have j1 := eq404 (τ X0) X1
       grind)
    | exact resolve eq17 eq404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq404
  have eq915 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 X1) ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq910 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq910
    | (have j0 := eq910 X0 X1
       grind)
    | exact resolve eq910 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq929 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (σ (τ X0)) X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq915 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq915
    | (have j0 := eq915 X0 X1
       grind)
    | exact resolve eq915 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq915
  have eq932 : ∀ X0 X1 : G, (k X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq929 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq929
    | (have j0 := eq929 X0 X1
       grind)
    | exact resolve eq929 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq997 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq932 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq932
    | (have j0 := eq932 X1 (σ X0)
       grind)
    | exact resolve eq932 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq932
  have eq1394 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (k X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq997 X0 X0
       have i₂ := eq389 X0 (σ X0)
       grind)
    | exact superpose eq389 eq997
    | (have j0 := eq997 X1 X0
       have j1 := eq389 X0 (σ X1)
       grind)
    | exact resolve eq997 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq997
  have eq1430 : ∀ X0 X1 : G, (k X0 (σ X1)) = X0 ∨ (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1394 X0 X1
       have j1 := eq421 X0 (σ X1)
       grind)
    | (have r₁ := eq1394 X0 X1
       have r₂ := eq421 X0 (σ X1)
       grind)
    | exact resolve eq1394 eq421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421 eq1394
  have eq1605 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (σ X1)
       have i₂ := eq1430 (σ X0) X1
       grind)
    | exact superpose eq1430 eq28
    | (have j1 := eq1430 (σ X0) X1
       grind)
    | exact resolve eq28 eq1430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1430
  have eq1616 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1605 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1605
    | (have j0 := eq1605 X0 X1
       grind)
    | exact resolve eq1605 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1605
  have eq1630 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (M.op (σ X0) (σ X1)) = (σ (M.op (τ (σ X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1616 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1616
    | (have j0 := eq1616 X0 X1
       grind)
    | exact resolve eq1616 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616
  have eq1639 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1630 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1630
    | (have j0 := eq1630 X0 X1
       grind)
    | exact resolve eq1630 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1630
  have eq1728 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1639 x y
       grind)
    | exact superpose eq1639 eq16
    | (have j1 := eq1639 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1639 x y
       grind)
    | exact resolve eq16 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1639
  have eq1751 : x = (k x y) := by grind
  clear eq1728
  have eq1928 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq390
       have i₂ := eq276 x y
       grind)
    | exact superpose eq276 eq390
    | (have j1 := eq276 x y
       grind)
    | exact resolve eq390 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1930 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (M.op x y) = (k x y) := by grind
  clear eq1928
  have eq1931 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1930
       have i₂ := eq1751
       grind)
    | exact superpose eq1751 eq1930
    | exact resolve eq1930 eq1751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1930
  have eq1932 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1931
       have i₂ := eq1751
       grind)
    | exact superpose eq1751 eq1931
    | exact resolve eq1931 eq1751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1931
  have eq1934 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq390
       have i₂ := eq1932
       grind)
    | exact superpose eq1932 eq390
    | exact resolve eq390 eq1932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390 eq1932
  have eq1947 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1934
  have eq1948 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1947
       have i₂ := eq1751
       grind)
    | exact superpose eq1751 eq1947
    | exact resolve eq1947 eq1751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1947
  have eq1949 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1948
  have eq1953 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1949
       grind)
    | exact superpose eq1949 eq16
    | exact resolve eq16 eq1949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1949
  have eq1983 : (σ x) ≠ (σ x) ∨ (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq1953
       have i₂ := eq276 x y
       grind)
    | exact superpose eq276 eq1953
    | (have j1 := eq276 x y
       grind)
    | exact resolve eq1953 eq276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq1985 : (M.op x y) = (k x y) := by grind
  clear eq1983
  have eq1987 : x = (M.op x y) := by
    first
    | (have i₁ := eq1985
       have i₂ := eq1751
       grind)
    | exact superpose eq1751 eq1985
    | exact resolve eq1985 eq1751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751 eq1985
  have eq1989 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1953
       have i₂ := eq1987
       grind)
    | exact superpose eq1987 eq1953
    | exact resolve eq1953 eq1987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953 eq1987
  have eq2004 : False := by grind
  exact eq2004
