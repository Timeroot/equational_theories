import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_y_pxy_pyy_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
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
  clear eq22
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
  have eq50 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op X3 (M.op X1 (M.op X3 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X1 X3 X4
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ X1 ∨ (M.op X0 (M.op X1 (M.op X0 X2))) = (k X1 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 (M.op X0 (M.op (M.op X0 X0) X2)) (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0) X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq79 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq44
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq44 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq103
    | exact resolve eq103 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq113 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq113
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq113
    | exact resolve eq113 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq127 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq114 eq79
    | (have j0 := eq79 (σ x) (σ y)
       grind)
    | exact resolve eq79 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq128 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq127
    | exact resolve eq127 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq131 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq128
       have r₂ := eq27
       grind)
    | exact resolve eq128 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq133 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq131
    | exact resolve eq131 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq224 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op x (M.op X1 (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq133 eq52
    | exact resolve eq52 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq252 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq237
    | (have j0 := eq237 (σ x)
       grind)
    | exact resolve eq237 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq133 eq252
    | exact resolve eq252 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq270 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq265
  have eq271 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq270
    | exact resolve eq270 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq278 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op (σ x) (M.op X0 (σ y)))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1
       have i₂ := eq237 X0
       grind)
    | exact superpose eq237 eq55
    | exact resolve eq55 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq291 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq299 : ∀ X1 : G, (M.op X1 X1) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    intro X1
    first
    | (have i₁ := eq278 X1 X1
       have i₂ := eq14 sF2 X1 sF3
       grind)
    | exact superpose eq14 eq278
    | exact resolve eq278 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq309 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq299 X1
       have i₂ := eq299 sF2
       grind)
    | exact superpose eq299 eq299
    | exact resolve eq299 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq323 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq271
       have i₂ := eq299 sF2
       grind)
    | exact superpose eq299 eq271
    | exact resolve eq271 eq299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271 eq299
  have eq328 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq323 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323
  have eq332 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq309 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq309
  have eq336 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op x (M.op X0 (M.op x y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq328 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq328
    | exact resolve eq328 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq350 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ X0 ∨ (M.op (σ x) (σ y)) = (k X0 X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq328 X0
       grind)
    | exact superpose eq328 eq13
    | (have r₁ := eq13 (M.op (σ x) (σ y)) (M.op (σ x) (σ y))
       have r₂ := eq328 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq13 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq956 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op x (M.op X0 X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq336 sF0
       have i₂ := eq332 sF0 x
       grind)
    | (have i₁ := eq336 sF0
       have i₂ := eq332 X0 sF0
       grind)
    | exact superpose eq332 eq336
    | exact resolve eq336 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332 eq336
  have eq970 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op x (M.op X0 X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq956 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq1636 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op X1 (M.op X0 X2)))) ≠ X3 ∨ (M.op X1 (M.op X0 (M.op X1 (M.op X0 X2)))) = (k X3 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq68 X1 X0 (M.op X0 X2)
       have i₂ := eq50 X0 X1 X2 X3 x
       grind)
    | (have i₁ := eq68 X1 X3 (M.op X3 x)
       have i₂ := eq50 X0 X1 X2 X3 x
       grind)
    | exact superpose eq50 eq68
    | exact resolve eq68 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq68
  have eq1668 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) ≠ X3 ∨ (M.op X1 (M.op X0 (M.op X1 (M.op X0 X2)))) = (k X3 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1636 X0 X1 X2 X3
       have i₂ := eq14 X0 X1 (M.op X0 X2)
       grind)
    | exact superpose eq14 eq1636
    | (have j0 := eq1636 X0 X1 X2 X3
       grind)
    | (have r₁ := eq1636 X0 X1 X2 (M.op X0 X0)
       have r₂ := eq14 X0 X1 (M.op X0 X2)
       grind)
    | exact resolve eq1636 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1636
  have eq1672 : ∀ X0 X3 : G, (M.op X0 X0) ≠ X3 ∨ (M.op X0 X0) = (k X3 X3) := by
    intro X0 X3
    first
    | (have i₁ := eq1668 X0 x x X3
       have i₂ := eq14 X0 x (M.op X0 x)
       grind)
    | exact superpose eq14 eq1668
    | (have j0 := eq1668 X0 x x X3
       grind)
    | (have r₁ := eq1668 X0 x x (M.op x (M.op X0 (M.op x x)))
       have r₂ := eq14 X0 x x
       grind)
    | exact resolve eq1668 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1668
  have eq6093 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq350 (M.op (σ x) (σ y))
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq6095 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq133 eq6093
    | exact resolve eq6093 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq6093
  have eq6100 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6095
  have eq6102 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6100 eq89
    | exact resolve eq89 eq6100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq6100
  have eq6106 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq6102
    | exact resolve eq6102 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq6102
  have eq6109 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq79 y y
       have i₂ := eq6106
       grind)
    | exact superpose eq6106 eq79
    | (have j0 := eq79 y y
       grind)
    | exact resolve eq79 eq6106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6106
  have eq6110 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq6109
  have eq6127 : y = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq328 y
       have i₂ := eq6110
       grind)
    | exact superpose eq6110 eq328
    | exact resolve eq328 eq6110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq6134 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq970 y
       have i₂ := eq6110
       grind)
    | exact superpose eq6110 eq970
    | exact resolve eq970 eq6110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970 eq6110
  have eq6155 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6134
  have eq6161 : y = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq6127
  have eq6169 : (M.op x y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6155
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6155
    | exact resolve eq6155 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6155
  have eq6293 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq6169 eq6161
    | exact resolve eq6161 eq6169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6161 eq6169
  have eq6294 : y = (M.op x y) := by grind
  clear eq6293
  have eq6318 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq6294 eq20
    | exact resolve eq20 eq6294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq6335 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq6318
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6318
    | exact resolve eq6318 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6318
  have eq6337 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq6335 eq26
    | exact resolve eq26 eq6335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq6779 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op x (M.op X1 y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq6294 eq224
    | exact resolve eq224 eq6294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq6913 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq51 eq6779
    | exact resolve eq6779 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq6779
  have eq6989 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq6913 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq6913
    | (have j0 := eq6913 X0
       grind)
    | exact resolve eq6913 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6913
  have eq7022 : ∀ X0 : G, (M.op x y) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq6294 eq6989
    | exact resolve eq6989 eq6294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6989
  have eq7027 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7022 X0
       have i₂ := eq291 X0 X0
       grind)
    | exact superpose eq291 eq7022
    | exact resolve eq7022 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291 eq7022
  have eq7029 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7027 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7027
    | (have j0 := eq7027 X0
       grind)
    | exact resolve eq7027 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq7027
  have eq7031 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | exact superpose eq6294 eq7029
    | exact resolve eq7029 eq6294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6294 eq7029
  have eq7111 : ∀ X1 : G, y ≠ X1 ∨ y = (k X1 X1) := by
    intro X1
    first
    | (have i₁ := eq1672 x x
       have i₂ := eq7031 x
       grind)
    | exact superpose eq7031 eq1672
    | (have r₁ := eq1672 x y
       have r₂ := eq7031 x
       grind)
    | exact resolve eq1672 eq7031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672
  have eq7131 : ∀ X1 : G, y = (M.op X1 y) := by
    intro X1
    first
    | (have i₁ := eq54 x (M.op x x) x
       have i₂ := eq7031 (M.op x x)
       grind)
    | exact superpose eq7031 eq54
    | exact resolve eq54 eq7031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq7364 : y = (k y y) := by
    first
    | (have j0 := eq7111 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7111
  have eq7372 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq7364
       grind)
    | exact superpose eq7364 eq77
    | exact resolve eq77 eq7364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq7364
  have eq7376 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6335 eq7372
    | exact resolve eq7372 eq6335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7372
  have eq7377 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq7376
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7376
    | exact resolve eq7376 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq7376
  have eq7378 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq6335 eq7377
    | exact resolve eq7377 eq6335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6335 eq7377
  have eq7381 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq7378 eq79
    | (have j0 := eq79 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq79 eq7378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq7378
  have eq7382 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq7381
  have eq7384 : y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq7382
       have i₂ := eq7031 sF1
       grind)
    | exact superpose eq7031 eq7382
    | exact resolve eq7382 eq7031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7031 eq7382
  have eq7397 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq7384 eq6337
    | exact resolve eq6337 eq7384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6337
  have eq7399 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7397
       have i₂ := eq7131 sF2
       grind)
    | exact superpose eq7131 eq7397
    | exact resolve eq7397 eq7131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7131 eq7397
  have eq7424 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq7399 eq27
    | exact resolve eq27 eq7399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq7399
  have eq7458 : False := by grind
  exact eq7458

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  have eq31 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq16 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq16
    | (have j0 := eq16 y
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq10
    | (have j0 := eq10 x X0
       grind)
    | exact resolve eq10 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq57 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 (M.op X0 X2))) X1) = (M.op (M.op X0 (M.op X1 (M.op X0 X2))) X1) := by
    intro X0 X1 X2
    grind
  have eq78 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq105 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq46
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq46 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq105
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq105
    | exact resolve eq105 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq112 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq111
    | exact resolve eq111 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq227 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq57 x X0
       have i₂ := eq57 x X1
       grind)
    | exact superpose eq57 eq57
    | exact resolve eq57 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq234 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq57 X1 X0
       grind)
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq929 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq78 X0
       have i₂ := eq57 X0 (σ X0)
       grind)
    | exact superpose eq57 eq78
    | exact resolve eq78 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq956 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq929 X0 X1
       have i₂ := eq234 X0 X0
       grind)
    | exact superpose eq234 eq929
    | (have j0 := eq929 X0 X1
       grind)
    | exact resolve eq929 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq929
  have eq974 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq956 X0 X1
       have i₂ := eq234 X0 X0
       grind)
    | exact superpose eq234 eq956
    | (have j0 := eq956 X0 X1
       grind)
    | exact resolve eq956 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq956
  have eq1160 : ∀ X0 X1 : G, (k (M.op X1 (M.op X0 X0)) X1) = (M.op (M.op X1 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 X0 X0
       have i₂ := eq57 X0 X1
       grind)
    | exact superpose eq57 eq68
    | exact resolve eq68 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq68
  have eq16566 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq112 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16567 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq16566
    | exact resolve eq16566 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16566
  have eq16578 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq16567
       have r₂ := eq29
       grind)
    | exact resolve eq16567 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16567
  have eq16582 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq16578
  have eq16625 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq16582
    | exact resolve eq16582 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16582
  have eq16843 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq16625 eq112
    | exact resolve eq112 eq16625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq16625
  have eq16852 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq16843
  have eq16855 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq16852
       have r₂ := eq29
       grind)
    | exact resolve eq16852 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16852
  have eq16860 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq16855
  have eq16901 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16860
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq16860
    | exact resolve eq16860 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16860
  have eq17589 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq46
       have i₂ := eq16901
       grind)
    | exact superpose eq16901 eq46
    | exact resolve eq46 eq16901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq16901
  have eq17605 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq22 eq17589
    | exact resolve eq17589 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17589
  have eq17702 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq17605 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq17605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17703 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq17702
  have eq17707 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq28 eq17703
    | exact resolve eq17703 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17703
  have eq17718 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq17707
       have r₂ := eq29
       grind)
    | exact resolve eq17707 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17707
  have eq17758 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq17718
  have eq17804 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq17758
    | exact resolve eq17758 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17758
  have eq18705 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq17804 eq17605
    | exact resolve eq17605 eq17804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17605 eq17804
  have eq18708 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq18705
  have eq18714 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq18708
       have r₂ := eq29
       grind)
    | exact resolve eq18708 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18708
  have eq18717 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq18714 eq31
    | exact resolve eq31 eq18714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq18714
  have eq18836 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq18717
    | exact resolve eq18717 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq18717
  have eq18837 : x = y := by grind
  clear eq18836
  have eq18838 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq18837
       grind)
    | exact superpose eq18837 eq20
    | exact resolve eq20 eq18837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq18839 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq18837
       grind)
    | exact superpose eq18837 eq26
    | exact resolve eq26 eq18837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq18837
  have eq18941 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq18839
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18839
    | exact resolve eq18839 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq18839
  have eq18942 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq18941 eq28
    | exact resolve eq28 eq18941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq18941
  have eq19062 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq18838
       have i₂ := eq227 x X0
       grind)
    | (have i₁ := eq18838
       have i₂ := eq227 X0 x
       grind)
    | exact superpose eq227 eq18838
    | exact resolve eq18838 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227 eq18838
  have eq19231 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18942 eq19062
    | exact resolve eq19062 eq18942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18942
  have eq19327 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 X0)) = (k (M.op x y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1160 X0 (M.op X0 X0)
       have i₂ := eq19062 (M.op X0 X0)
       grind)
    | exact superpose eq19062 eq1160
    | exact resolve eq1160 eq19062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq19407 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq19327 x
       have i₂ := eq19062 x
       grind)
    | exact superpose eq19062 eq19327
    | exact resolve eq19327 eq19062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19327
  have eq19504 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq19407
       have i₂ := eq19062 sF0
       grind)
    | exact superpose eq19062 eq19407
    | exact resolve eq19407 eq19062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19407
  have eq19543 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq19231 eq29
    | exact resolve eq29 eq19231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq19231
  have eq20944 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq19504 eq974
    | (have j0 := eq974 X0 (M.op x y)
       grind)
    | exact resolve eq974 eq19504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974 eq19504
  have eq20953 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq20944 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20944
  have eq20959 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq22 eq20953
    | (have j0 := eq20953 X0
       grind)
    | exact resolve eq20953 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq20953
  have eq20968 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq20959 x
       have i₂ := eq19062 x
       grind)
    | exact superpose eq19062 eq20959
    | exact resolve eq20959 eq19062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19062 eq20959
  have eq20972 : False := by grind
  exact eq20972

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pyy_pxx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq76 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq101 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq113 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
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
    | (have j0 := eq113 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq113 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq113 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq128 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq101
       have i₂ := eq115 sF3
       grind)
    | exact superpose eq115 eq101
    | exact resolve eq101 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq129 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq128
       have i₂ := eq115 y
       grind)
    | exact superpose eq115 eq128
    | exact resolve eq128 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq139 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq142 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq139
       have i₂ := eq115 sF1
       grind)
    | exact superpose eq115 eq139
    | exact resolve eq139 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq145 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq142
       have i₂ := eq115 sF0
       grind)
    | exact superpose eq115 eq142
    | exact resolve eq142 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq142
  have eq290 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x X0
       have i₂ := eq55 x X1
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq363 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq145
       have i₂ := eq290 sF0 x
       grind)
    | (have i₁ := eq145
       have i₂ := eq290 X0 sF0
       grind)
    | exact superpose eq290 eq145
    | exact resolve eq145 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op x (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq363 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq363
    | exact resolve eq363 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq363
  have eq1403 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq76 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X0)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq76 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq76 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq12 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1441 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1444 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1403 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403
  have eq1445 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1444 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1444
  have eq1450 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1445 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq1445
    | (have j0 := eq1445 X0 X1
       grind)
    | exact resolve eq1445 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1445
  have eq25968 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1450 X0 X1
       have j1 := eq1441 X0 X1
       grind)
    | (have r₁ := eq1450 X0 X1
       have r₂ := eq1441 X0 X1
       grind)
    | (have r₁ := eq1450 X0 X0
       have r₂ := eq1441 X0 X0
       grind)
    | exact resolve eq1450 eq1441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1441 eq1450
  have eq26072 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq25968 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq25968
    | exact resolve eq25968 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26148 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq25968 X0 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq25968
    | (have j0 := eq25968 X0 y
       grind)
    | exact resolve eq25968 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25968
  have eq26504 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq26072 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq26072
    | (have j0 := eq26072 X0 X1
       grind)
    | exact resolve eq26072 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq26072
  have eq40411 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq26148 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq26148
    | (have j0 := eq26148 x
       grind)
    | exact resolve eq26148 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq26148
  have eq40451 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq40411
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq40411
    | exact resolve eq40411 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40411
  have eq40483 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq40451
    | exact resolve eq40451 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40451
  have eq40867 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq26504 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq26504
    | (have j0 := eq26504 X1 X1
       grind)
    | exact resolve eq26504 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26504
  have eq41503 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq40867 x y
       grind)
    | exact superpose eq40867 eq44
    | (have j1 := eq40867 x y
       grind)
    | exact resolve eq44 eq40867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq40867
  have eq41704 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq41503
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq41503
    | exact resolve eq41503 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41503
  have eq41818 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq41704
    | exact resolve eq41704 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41704
  have eq41838 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq41818 eq40483
    | exact resolve eq40483 eq41818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40483 eq41818
  have eq41845 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq41838
       have r₂ := eq27
       grind)
    | exact resolve eq41838 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41838
  have eq42086 : (τ (σ y)) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq41845 eq129
    | exact resolve eq129 eq41845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq41845
  have eq42206 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq42086
    | exact resolve eq42086 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq42086
  have eq42207 : y = (M.op y y) := by grind
  clear eq42206
  have eq42216 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq42207
       have i₂ := eq290 y X0
       grind)
    | (have i₁ := eq42207
       have i₂ := eq290 X0 y
       grind)
    | exact superpose eq290 eq42207
    | exact resolve eq42207 eq290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq290 eq42207
  have eq42544 : ∀ X1 : G, y = (M.op X1 y) := by
    intro X1
    first
    | (have i₁ := eq54 x (M.op x x) x
       have i₂ := eq42216 (M.op x x)
       grind)
    | exact superpose eq42216 eq54
    | exact resolve eq54 eq42216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq42620 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq426 sF0
       have i₂ := eq42216 sF0
       grind)
    | exact superpose eq42216 eq426
    | exact resolve eq426 eq42216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq42664 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq145
       have i₂ := eq42216 sF0
       grind)
    | exact superpose eq42216 eq145
    | exact resolve eq145 eq42216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq42732 : y = (σ y) := by
    first
    | (have i₁ := eq42664
       have i₂ := eq42216 sF1
       grind)
    | exact superpose eq42216 eq42664
    | exact resolve eq42664 eq42216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42664
  have eq42764 : y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq42620
       have i₂ := eq42216 sF1
       grind)
    | exact superpose eq42216 eq42620
    | exact resolve eq42620 eq42216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42216 eq42620
  have eq42940 : y = (σ y) := by
    first
    | (have i₁ := eq42732
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq42732
    | exact resolve eq42732 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq42732
  have eq42961 : y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq42764
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq42764
    | exact resolve eq42764 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq42764
  have eq43024 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq20 eq42961
    | exact resolve eq42961 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq42961
  have eq43322 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq42940 eq26
    | exact resolve eq26 eq42940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq42940
  have eq45677 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq43322
       have i₂ := eq42544 sF2
       grind)
    | exact superpose eq42544 eq43322
    | exact resolve eq43322 eq42544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42544 eq43322
  have eq46675 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq45677 eq27
    | exact resolve eq27 eq45677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq45677
  have eq46686 : False := by grind
  exact eq46686

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else X`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxx_pxy_x_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ X1 ∨ (M.op X3 X3) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X1
       have i₂ := eq9 X1 X0 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X3 X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ (M.op X3 X3) ∨ (M.op X0 (M.op X1 (M.op X0 X2))) = X1 ∨ (k X3 X1) = (M.op X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X3 X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op X2 (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X3
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X2 X2) ∨ (M.op X2 X2) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 X1 X2
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X2
       have i₂ := eq22 X0 X2
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87 X0 X1 X2
       have i₂ := eq21 X0 X0 X1
       grind)
    | exact superpose eq21 eq87
    | exact resolve eq87 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq87
  have eq94 : ∀ X1 X2 : G, (M.op X2 X2) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X1 X2
    first
    | (have j0 := eq82 x X1 X2
       grind)
    | (have r₁ := eq82 x X1 X1
       have r₂ := eq22 x X1
       grind)
    | exact resolve eq82 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq82
  have eq96 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X2 (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq80 X0 X1 X2 X3
       have i₂ := eq89 X0 X0
       grind)
    | exact superpose eq89 eq80
    | exact resolve eq80 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq89
  have eq107 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = X1 ∨ (k X3 X1) = (M.op X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq61 X0 X1 X2 X3
       grind)
    | (have r₁ := eq61 X2 X1 X3 X0
       have r₂ := eq96 X0 X1 X2 X3
       grind)
    | exact resolve eq61 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq96
  have eq252 : ∀ X0 X3 X4 : G, X0 ≠ X0 ∨ (M.op X3 X3) = (k X3 X0) ∨ (k X4 X0) = (M.op X4 X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq24 x X0 x X3
       have i₂ := eq107 x X0 x X4
       grind)
    | exact superpose eq107 eq24
    | (have j0 := eq24 X0 X0 x X3
       have j1 := eq107 X0 X0 x X4
       grind)
    | (have r₁ := eq24 X0 x x X3
       have r₂ := eq107 X0 x x X3
       grind)
    | exact resolve eq24 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq107
  have eq270 : ∀ X0 X3 X4 : G, (M.op X3 X3) = (k X3 X0) ∨ (k X4 X0) = (M.op X4 X0) := by
    intro X0 X3 X4
    first
    | (have j0 := eq252 X0 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq655 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op X2 X0) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq92 X0 X1 X2
       have i₂ := eq94 X3 X0
       grind)
    | exact superpose eq94 eq92
    | (have j1 := eq94 X3 X0
       grind)
    | exact resolve eq92 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq94
  have eq883 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq270 X1 x X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq885 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq883 X0 X1
       have j1 := eq655 X1 X1 x X0
       grind)
    | (have r₁ := eq883 x X0
       have r₂ := eq655 X0 x x x
       grind)
    | (have r₁ := eq883 X1 X1
       have r₂ := eq655 X1 X1 X1 x
       grind)
    | exact resolve eq883 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655 eq883
  have eq889 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq885 (σ X0) (σ X1)
       grind)
    | exact superpose eq885 eq15
    | exact resolve eq15 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq898 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq889 X0 X1
       have i₂ := eq885 X0 X1
       grind)
    | exact superpose eq885 eq889
    | exact resolve eq889 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885 eq889
  have eq900 : False := by grind
  exact eq900

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else Y`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pxx_pxy_y_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 1)
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ X1 ∨ (M.op X3 X3) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X1
       have i₂ := eq9 X1 X0 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X3 X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ (M.op X3 X3) ∨ (M.op X0 (M.op X1 (M.op X0 X2))) = X1 ∨ (k X3 X1) = (M.op X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X3 X1
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X0 X0)) = (M.op X2 (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X3
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X2 X2) ∨ (M.op X2 X2) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 X1 X2
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X2
       have i₂ := eq22 X0 X2
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 X1
       have i₂ := eq22 X1 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87 X0 X1 X2
       have i₂ := eq21 X0 X0 X1
       grind)
    | exact superpose eq21 eq87
    | exact resolve eq87 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq87
  have eq94 : ∀ X1 X2 : G, (M.op X2 X2) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X1 X2
    first
    | (have j0 := eq82 x X1 X2
       grind)
    | (have r₁ := eq82 x X1 X1
       have r₂ := eq22 x X1
       grind)
    | exact resolve eq82 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq82
  have eq96 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op X2 (M.op X1 (M.op X2 X3))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq80 X0 X1 X2 X3
       have i₂ := eq89 X0 X0
       grind)
    | exact superpose eq89 eq80
    | exact resolve eq80 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq89
  have eq107 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = X1 ∨ (k X3 X1) = (M.op X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq61 X0 X1 X2 X3
       grind)
    | (have r₁ := eq61 X2 X1 X3 X0
       have r₂ := eq96 X0 X1 X2 X3
       grind)
    | exact resolve eq61 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq96
  have eq252 : ∀ X0 X3 X4 : G, X0 ≠ X0 ∨ (M.op X3 X3) = (k X3 X0) ∨ (k X4 X0) = (M.op X4 X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq24 x X0 x X3
       have i₂ := eq107 x X0 x X4
       grind)
    | exact superpose eq107 eq24
    | (have j0 := eq24 X0 X0 x X3
       have j1 := eq107 X0 X0 x X4
       grind)
    | (have r₁ := eq24 X0 x x X3
       have r₂ := eq107 X0 x x X3
       grind)
    | exact resolve eq24 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq107
  have eq270 : ∀ X0 X3 X4 : G, (M.op X3 X3) = (k X3 X0) ∨ (k X4 X0) = (M.op X4 X0) := by
    intro X0 X3 X4
    first
    | (have j0 := eq252 X0 X3 X4
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq655 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op X2 X0) ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq92 X0 X1 X2
       have i₂ := eq94 X3 X0
       grind)
    | exact superpose eq94 eq92
    | (have j1 := eq94 X3 X0
       grind)
    | exact resolve eq92 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq94
  have eq883 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq270 X1 x X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq885 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq883 X0 X1
       have j1 := eq655 X1 X1 x X0
       grind)
    | (have r₁ := eq883 x X0
       have r₂ := eq655 X0 x x x
       grind)
    | (have r₁ := eq883 X1 X1
       have r₂ := eq655 X1 X1 X1 x
       grind)
    | exact resolve eq883 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655 eq883
  have eq889 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq885 (σ X0) (σ X1)
       grind)
    | exact superpose eq885 eq15
    | exact resolve eq15 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq898 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq889 X0 X1
       have i₂ := eq885 X0 X1
       grind)
    | exact superpose eq885 eq889
    | exact resolve eq889 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885 eq889
  have eq900 : False := by grind
  exact eq900

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyy_pxy_pyy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X2 X2) = (k X0 X2) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X2
       have j1 := eq14 X0 X2
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 (M.op X1 X1) X1
       have r₂ := eq14 X0 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq64 (k X0 X1) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq64 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq64 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq68 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = X2 ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X2 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq58 X0 X1 X2
       have j1 := eq12 X0 X2
       grind)
    | (have r₁ := eq58 X1 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq58 X0 X1 (M.op (M.op X0 X0) (M.op X0 X0))
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq58 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq58 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq90 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X2) = (k X1 X2) ∨ (M.op X2 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq68 X0 X1 X2
       have j1 := eq65 (M.op X1 X1) X0
       grind)
    | (have r₁ := eq68 X1 X1 X0
       have r₂ := eq65 X0 X1
       grind)
    | (have r₁ := eq68 X0 X1 (M.op X1 X1)
       have r₂ := eq65 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq68 X0 X1 X1
       have r₂ := eq65 (k X1 X1) X1
       grind)
    | exact resolve eq68 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq68
  have eq111 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq22 x X0
       have i₂ := eq22 x X1
       grind)
    | exact superpose eq22 eq22
    | exact resolve eq22 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X2 X2) ∨ (M.op X2 X2) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X2
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 X1 X2
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 X2 X2
       have i₂ := eq22 X0 X2
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq119 X0 X1 X2
       have i₂ := eq21 X0 X0 X1
       grind)
    | exact superpose eq21 eq119
    | exact resolve eq119 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq119
  have eq126 : ∀ X1 X2 : G, (M.op X2 X2) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X1 X2
    first
    | (have j0 := eq114 x X1 X2
       grind)
    | (have r₁ := eq114 x X1 X1
       have r₂ := eq22 x X1
       grind)
    | exact resolve eq114 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq114
  have eq129 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k X1 X2) ∨ (M.op X2 X2) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq90 X0 X1 X2
       grind)
    | (have r₁ := eq90 X0 X1 X2
       have r₂ := eq111 X0 X1
       grind)
    | (have r₁ := eq90 X1 X0 X2
       have r₂ := eq111 X0 X1
       grind)
    | exact resolve eq90 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq200 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq129 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq775 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op X2 X0) ∨ (M.op X3 X0) = (k X3 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq124 X0 X1 X2
       have i₂ := eq126 X3 X0
       grind)
    | exact superpose eq126 eq124
    | (have j1 := eq126 X3 X0
       grind)
    | exact resolve eq124 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq126
  have eq999 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X1) ∨ (k X2 X1) = (M.op X2 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq200 X2 X1
       have i₂ := eq111 X1 X0
       grind)
    | (have i₁ := eq200 X2 X1
       have i₂ := eq111 X0 X1
       grind)
    | exact superpose eq111 eq200
    | (have j0 := eq200 X2 X1
       grind)
    | (have r₁ := eq200 X1 X1
       have r₂ := eq111 X1 X1
       grind)
    | (have r₁ := eq200 X0 X0
       have r₂ := eq111 X0 X0
       grind)
    | exact resolve eq200 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq200
  have eq1031 : ∀ X1 X2 : G, (k X2 X1) = (M.op X2 X1) := by
    intro X1 X2
    first
    | (have j0 := eq999 x X1 X2
       have j1 := eq775 X1 X1 X2 X2
       grind)
    | (have r₁ := eq999 X1 x X2
       have r₂ := eq775 x X1 X2 x
       grind)
    | (have r₁ := eq999 x X1 X1
       have r₂ := eq775 x X1 x x
       grind)
    | exact resolve eq999 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775 eq999
  have eq5829 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq1031 (σ X1) (σ X0)
       grind)
    | exact superpose eq1031 eq15
    | exact resolve eq15 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5844 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5829 X0 X1
       have i₂ := eq1031 X1 X0
       grind)
    | exact superpose eq1031 eq5829
    | exact resolve eq5829 eq1031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031 eq5829
  have eq5864 : False := by grind
  exact eq5864

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxy_x_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 X1 X1
       have i₂ := eq9 X1 X0 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ X1 ∨ (k X3 X1) = (M.op X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X3 X1
       have i₂ := eq9 X1 X0 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X3 X1
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = X2 ∨ (M.op X2 X2) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq14
    | (have j0 := eq14 X2 X2
       grind)
    | exact resolve eq14 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq100 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = X2 ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq90 X0 X1 X2
       have j1 := eq12 X1 X2
       grind)
    | (have r₁ := eq90 X0 X1 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))
       have r₂ := eq12 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq90 X0 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq90 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq297 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (k X4 X1) = (M.op X4 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq25 X0 X1 (M.op x (M.op X1 (M.op x x))) X4
       have i₂ := eq21 x X1 x X0
       grind)
    | exact superpose eq21 eq25
    | (have j0 := eq25 X0 X1 x X4
       grind)
    | exact resolve eq25 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq25
  have eq308 : ∀ X1 X4 : G, (k X4 X1) = (M.op X4 X1) := by
    intro X1 X4
    first
    | (have j0 := eq297 x X1 X4
       have j1 := eq100 x X4 X1
       grind)
    | (have r₁ := eq297 x x X4
       have r₂ := eq100 x X1 x
       grind)
    | (have r₁ := eq297 x (M.op x (M.op x x)) X4
       have r₂ := eq100 x X1 (M.op x (M.op x x))
       grind)
    | (have r₁ := eq297 X1 (k X1 (M.op X1 X1)) X4
       have r₂ := eq100 x X1 (M.op X1 X1)
       grind)
    | exact resolve eq297 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq297
  have eq583 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq308 (σ X1) (σ X0)
       grind)
    | exact superpose eq308 eq15
    | exact resolve eq15 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq583 X0 X1
       have i₂ := eq308 X1 X0
       grind)
    | exact superpose eq308 eq583
    | exact resolve eq583 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308 eq583
  have eq591 : False := by grind
  exact eq591

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxx_x_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  have eq51 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X1 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ X1 ∨ (M.op X3 X3) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X3 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq76 : x ≠ (M.op x y) ∨ y = (M.op y y) ∨ x = (k x y) := by
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
  have eq77 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq103
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq103
    | exact resolve eq103 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq116 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq134 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq241 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x X0
       have i₂ := eq55 x X1
       grind)
    | exact superpose eq55 eq55
    | exact resolve eq55 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq55 X1 X0
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 : G, (M.op x x) = (M.op X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq51 eq54
    | exact resolve eq54 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq52 eq54
    | exact resolve eq54 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq524 : ∀ X0 : G, (M.op x x) ≠ (M.op (M.op x y) (M.op x y)) ∨ (M.op X0 X0) = (k X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq409 eq13
    | (have j0 := eq13 X0 (M.op (M.op x y) (M.op x y))
       grind)
    | exact resolve eq13 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq537 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq524 X0
       grind)
    | (have r₁ := eq524 X0
       have r₂ := eq241 x (M.op x y)
       grind)
    | (have r₁ := eq524 X0
       have r₂ := eq241 (M.op x y) x
       grind)
    | exact resolve eq524 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq554 : ∀ X0 : G, (M.op (σ x) (σ x)) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq410 eq13
    | (have j0 := eq13 X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq13 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq567 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have j0 := eq554 X0
       grind)
    | (have r₁ := eq554 X0
       have r₂ := eq241 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq554 X0
       have r₂ := eq241 (M.op (σ x) (σ y)) (σ x)
       grind)
    | exact resolve eq554 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq1115 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (M.op X4 X4) = (k X4 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq66 X0 X1 (M.op x (M.op X1 (M.op x x))) X4
       have i₂ := eq53 x X1 x X0
       grind)
    | exact superpose eq53 eq66
    | (have j0 := eq66 X0 X1 x X4
       grind)
    | exact resolve eq66 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq66
  have eq1142 : ∀ X0 X1 X4 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X4 X4) = (k X4 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq1115 X0 X1 X4
       have i₂ := eq249 X0 X0
       grind)
    | exact superpose eq249 eq1115
    | (have j0 := eq1115 X0 X1 X4
       grind)
    | (have r₁ := eq1115 X0 (M.op X0 X0) X4
       have r₂ := eq249 X0 X0
       grind)
    | exact resolve eq1115 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1315 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X0
       have i₂ := eq55 X0 (σ X0)
       grind)
    | exact superpose eq55 eq95
    | exact resolve eq95 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1322 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq95 X0 X0
       grind)
    | exact superpose eq95 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq95 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq95 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq13 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1324 : ∀ X0 : G, (M.op x (M.op (σ X0) (M.op x y))) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (σ X0)
       have i₂ := eq95 X0 X0
       grind)
    | exact superpose eq95 eq51
    | (have j1 := eq95 X0 X0
       grind)
    | exact resolve eq51 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1347 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq1365 : ∀ X0 : G, (M.op x (M.op (σ X0) (M.op x y))) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1324 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq1367 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1322 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1322
  have eq1374 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1315 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq1382 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1367 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq1367 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq1367 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367
  have eq1383 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1374 X0 X1
       have i₂ := eq249 X0 X0
       grind)
    | exact superpose eq249 eq1374
    | (have j0 := eq1374 X0 X1
       grind)
    | exact resolve eq1374 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374
  have eq1400 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1383 X0 X1
       have i₂ := eq249 X0 X0
       grind)
    | exact superpose eq249 eq1383
    | (have j0 := eq1383 X0 X1
       grind)
    | exact resolve eq1383 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq1383
  have eq1540 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op (M.op x y) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq537 X1
       have i₂ := eq241 X1 X0
       grind)
    | (have i₁ := eq537 X1
       have i₂ := eq241 X0 X1
       grind)
    | exact superpose eq241 eq537
    | exact resolve eq537 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq1634 : ∀ X0 : G, (M.op x (M.op X0 (M.op x y))) = (k X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq567 X0
       have i₂ := eq51 X0
       grind)
    | exact superpose eq51 eq567
    | exact resolve eq567 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1639 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq567 X1
       have i₂ := eq241 X1 X0
       grind)
    | (have i₁ := eq567 X1
       have i₂ := eq241 X0 X1
       grind)
    | exact superpose eq241 eq567
    | exact resolve eq567 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1947 : ∀ X0 X1 : G, (k X1 (σ (M.op (M.op x y) (M.op x y)))) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq1540 eq34
    | exact resolve eq34 eq1540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1540
  have eq2035 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (k X1 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq1639 eq34
    | exact resolve eq34 eq1639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1639
  have eq7083 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (σ (k X0 X0))) ∨ (σ X0) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X2 X1
       have i₂ := eq1400 X2 X0
       grind)
    | exact superpose eq1400 eq55
    | (have j1 := eq1400 X2 X0
       grind)
    | exact resolve eq55 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq7166 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X1)
       have i₂ := eq1400 X0 (τ X1)
       grind)
    | exact superpose eq1400 eq34
    | (have j1 := eq1400 X0 (τ X1)
       grind)
    | exact resolve eq34 eq1400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq1400
  have eq7195 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7166 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq7166
    | (have j0 := eq7166 X0 X1
       grind)
    | exact resolve eq7166 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7166
  have eq7271 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7195 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq7195
    | (have j0 := eq7195 X0 X1
       grind)
    | exact resolve eq7195 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7195
  have eq8074 : ∀ X0 X2 : G, (σ (M.op X0 X0)) = (σ (M.op X2 X2)) := by
    intro X0 X2
    first
    | exact superpose eq1947 eq1947
    | exact resolve eq1947 eq1947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1947
  have eq10055 : ∀ X0 : G, (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ≠ (σ (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (M.op X0 X0) = (k X0 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq567 eq1382
    | (have j0 := eq1382 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0
       grind)
    | exact resolve eq1382 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382
  have eq10077 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have j0 := eq10055 X0
       grind)
    | (have r₁ := eq10055 X0
       have r₂ := eq8074 (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq10055 X0
       have r₂ := eq8074 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq10055 eq8074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8074 eq10055
  have eq10105 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | (have i₁ := eq10077 X1
       have i₂ := eq241 X1 X0
       grind)
    | (have i₁ := eq10077 X1
       have i₂ := eq241 X0 X1
       grind)
    | exact superpose eq241 eq10077
    | exact resolve eq10077 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10145 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | exact superpose eq2035 eq10077
    | exact resolve eq10077 eq2035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2035
  have eq10264 : (M.op (σ y) (σ y)) = (σ (k y (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq10077 eq36
    | exact resolve eq36 eq10077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq10077
  have eq10291 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq567 eq10264
    | exact resolve eq10264 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567 eq10264
  have eq10378 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq10291
       grind)
    | exact superpose eq10291 eq16
    | exact resolve eq16 eq10291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10291
  have eq10683 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 x) X1 x
       have i₂ := eq10145 X0 (M.op X1 x)
       grind)
    | exact superpose eq10145 eq14
    | exact resolve eq14 eq10145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10729 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 X1)
       have i₂ := eq10145 X1 X0
       grind)
    | exact superpose eq10145 eq16
    | exact resolve eq16 eq10145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13621 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq10105 eq10
    | exact resolve eq10 eq10105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10105
  have eq13654 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op x (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq1634 eq13621
    | exact resolve eq13621 eq1634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1634 eq13621
  have eq19007 : (σ (k y y)) = (M.op x (M.op (σ y) (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1365 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1365
    | (have j0 := eq1365 y
       grind)
    | exact resolve eq1365 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19008 : (σ (k (M.op x y) (M.op x y))) = (M.op x (M.op (σ (M.op x y)) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq1365
    | (have j0 := eq1365 (M.op x y)
       grind)
    | exact resolve eq1365 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1365
  have eq19129 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq51 eq19008
    | exact resolve eq19008 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19008
  have eq19130 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq51 eq19007
    | exact resolve eq19007 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19007
  have eq19150 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq134 eq19129
    | exact resolve eq19129 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19129
  have eq19151 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq19130
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq19130
    | exact resolve eq19130 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq19130
  have eq19159 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq1142 x (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq19150
       have r₂ := eq1142 (σ (M.op x y)) (k (σ (M.op x y)) (σ (M.op x y))) x
       grind)
    | (have r₁ := eq19150
       have r₂ := eq1142 (σ (M.op x y)) (σ (M.op x y)) x
       grind)
    | exact resolve eq19150 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19150
  have eq19160 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq1142 x (σ y) (σ y)
       grind)
    | (have r₁ := eq19151
       have r₂ := eq1142 (σ y) (k (σ y) (σ y)) x
       grind)
    | (have r₁ := eq19151
       have r₂ := eq1142 (σ y) (σ y) x
       grind)
    | exact resolve eq19151 eq1142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1142 eq19151
  have eq19171 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq19160 eq89
    | exact resolve eq89 eq19160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq19176 : (k y y) = (M.op y y) := by
    first
    | exact superpose eq10378 eq19171
    | exact resolve eq19171 eq10378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19171
  have eq49861 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq7271 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7271
  have eq50103 : ∀ X0 : G, y ≠ (M.op y y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq49861 X0 y
       have i₂ := eq19176
       grind)
    | exact superpose eq19176 eq49861
    | (have j0 := eq49861 X0 y
       grind)
    | exact resolve eq49861 eq19176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19176
  have eq50107 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq19160 eq49861
    | (have j0 := eq49861 X0 (σ y)
       grind)
    | exact resolve eq49861 eq19160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19160 eq49861
  have eq50111 : ∀ X0 X1 : G, (M.op X0 X0) ≠ y ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq50103 X1
       have i₂ := eq241 y X0
       grind)
    | (have i₁ := eq50103 X1
       have i₂ := eq241 X0 y
       grind)
    | exact superpose eq241 eq50103
    | (have j0 := eq50103 X1
       grind)
    | exact resolve eq50103 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50103
  have eq50119 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ y) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq50107 X0
       have i₂ := eq241 sF3 X1
       grind)
    | (have i₁ := eq50107 X0
       have i₂ := eq241 X0 sF3
       grind)
    | exact superpose eq241 eq50107
    | (have j0 := eq50107 X1
       grind)
    | exact resolve eq50107 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50107
  have eq50789 : ∀ X0 X2 : G, (σ y) ≠ (σ (M.op X0 X0)) ∨ (σ y) = (M.op X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq50119 x X2
       have i₂ := eq10145 X0 x
       grind)
    | exact superpose eq10145 eq50119
    | (have j0 := eq50119 X0 X2
       grind)
    | exact resolve eq50119 eq10145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10145
  have eq58817 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58824 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq58817
    | exact resolve eq58817 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58817
  have eq58829 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq58824
       have r₂ := eq27
       grind)
    | exact resolve eq58824 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58824
  have eq58831 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq58829
    | exact resolve eq58829 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58829
  have eq58836 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq58831 eq10378
    | exact resolve eq10378 eq58831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58831
  have eq58963 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq58836
    | exact resolve eq58836 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58836
  have eq58964 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq58963
  have eq58968 : ∀ X0 : G, (M.op X0 X0) = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq58964
       have i₂ := eq241 y X0
       grind)
    | (have i₁ := eq58964
       have i₂ := eq241 X0 y
       grind)
    | exact superpose eq241 eq58964
    | exact resolve eq58964 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59019 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq10683 y x
       have i₂ := eq58964
       grind)
    | exact superpose eq58964 eq10683
    | exact resolve eq10683 eq58964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10683
  have eq59062 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq50789 y X0
       have i₂ := eq58964
       grind)
    | exact superpose eq58964 eq50789
    | (have j0 := eq50789 X0 X0
       grind)
    | exact resolve eq50789 eq58964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58964
  have eq59082 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq59062 X0
       grind)
    | (have r₁ := eq59062 X0
       have r₂ := eq24
       grind)
    | exact resolve eq59062 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59062
  have eq59101 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq59019 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq59019
    | (have j0 := eq59019 X0
       grind)
    | exact resolve eq59019 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59019
  have eq59663 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13654 X0 sF0
       have i₂ := eq58968 sF0
       grind)
    | exact superpose eq58968 eq13654
    | exact resolve eq13654 eq58968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13654 eq58968
  have eq59760 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq59663 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59663
    | (have j0 := eq59663 X0
       grind)
    | exact resolve eq59663 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59663
  have eq59884 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq20 eq59760
    | (have j0 := eq59760 X0
       grind)
    | exact resolve eq59760 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59760
  have eq60788 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52 sF4
       have i₂ := eq59082 sF4
       grind)
    | exact superpose eq59082 eq52
    | exact resolve eq52 eq59082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59082
  have eq60860 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq60788
    | exact resolve eq60788 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60788
  have eq61293 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq60860 eq27
    | exact resolve eq27 eq60860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60860
  have eq62639 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq59101 sF3
       have i₂ := eq59884 sF3
       grind)
    | exact superpose eq59884 eq59101
    | exact resolve eq59101 eq59884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59101 eq59884
  have eq62698 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq62639
  have eq62726 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq62698
       have r₂ := eq61293
       grind)
    | exact resolve eq62698 eq61293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61293 eq62698
  have eq62819 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq62726 eq27
    | exact resolve eq27 eq62726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62821 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq62726 eq77
    | (have r₁ := eq77
       have r₂ := eq62726
       grind)
    | exact resolve eq77 eq62726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq62726
  have eq62837 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq62821
  have eq76520 : ∀ X0 : G, (M.op X0 X0) = (τ (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq62837 eq10729
    | exact resolve eq10729 eq62837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10729 eq62837
  have eq76603 : ∀ X0 : G, (σ x) = (k (σ x) (σ y)) ∨ (M.op X0 X0) = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq76520
    | exact resolve eq76520 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76520
  have eq78907 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ (M.op X0 X0) = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq76603 eq117
    | (have j1 := eq76603 y
       grind)
    | exact resolve eq117 eq76603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq76603
  have eq78919 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op y y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq78907 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78907
  have eq78923 : ∀ X0 : G, x = (M.op x y) ∨ y = (M.op y y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have j0 := eq78919 y
       grind)
    | (have r₁ := eq78919 X0
       have r₂ := eq62819
       grind)
    | exact resolve eq78919 eq62819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62819 eq78919
  have eq78929 : y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have j0 := eq78923 y
       have j1 := eq50111 x y
       grind)
    | (have r₁ := eq78923 x
       have r₂ := eq50111 y x
       grind)
    | (have r₁ := eq78923 x
       have r₂ := eq50111 x x
       grind)
    | exact resolve eq78923 eq50111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50111 eq78923
  have eq78931 : ∀ X0 : G, (M.op X0 X0) = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq78929
       have i₂ := eq241 y X0
       grind)
    | (have i₁ := eq78929
       have i₂ := eq241 X0 y
       grind)
    | exact superpose eq241 eq78929
    | exact resolve eq78929 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79031 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq50789 y X0
       have i₂ := eq78929
       grind)
    | exact superpose eq78929 eq50789
    | (have j0 := eq50789 X0 X0
       grind)
    | exact resolve eq50789 eq78929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78929
  have eq79059 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq79031 X0
       grind)
    | (have r₁ := eq79031 X0
       have r₂ := eq24
       grind)
    | exact resolve eq79031 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79031
  have eq79478 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq51 sF0
       have i₂ := eq78931 sF0
       grind)
    | exact superpose eq78931 eq51
    | exact resolve eq51 eq78931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq78931
  have eq79662 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79478
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq79478
    | exact resolve eq79478 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79478
  have eq79782 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq79662 eq20
    | exact resolve eq20 eq79662
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79662
  have eq79943 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq79782
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq79782
    | exact resolve eq79782 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79782
  have eq80479 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq52 sF4
       have i₂ := eq79059 sF4
       grind)
    | exact superpose eq79059 eq52
    | exact resolve eq52 eq79059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79059
  have eq80588 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq80479
    | exact resolve eq80479 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80479
  have eq80753 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq80588 eq27
    | exact resolve eq27 eq80588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80588
  have eq80785 : x = (M.op x y) := by
    first
    | (have r₁ := eq80753
       have r₂ := eq79943
       grind)
    | exact resolve eq80753 eq79943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79943 eq80753
  have eq80789 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq80785 eq20
    | exact resolve eq20 eq80785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80795 : x ≠ x ∨ y = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq80785 eq76
    | (have r₁ := eq76
       have r₂ := eq80785
       grind)
    | exact resolve eq76 eq80785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq80894 : y = (M.op y y) ∨ x = (k x y) := by grind
  clear eq80795
  have eq80949 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq80789
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq80789
    | exact resolve eq80789 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80789
  have eq89117 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (σ y) ∨ x = (k x y) := by
    intro X0
    first
    | (have i₁ := eq50789 y X0
       have i₂ := eq80894
       grind)
    | exact superpose eq80894 eq50789
    | (have j0 := eq50789 X0 X0
       grind)
    | exact resolve eq50789 eq80894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50789 eq80894
  have eq89141 : ∀ X0 : G, x = (k x y) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq89117 X0
       grind)
    | (have r₁ := eq89117 X0
       have r₂ := eq24
       grind)
    | exact resolve eq89117 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89117
  have eq89320 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1347 x y
       have i₂ := eq89141 X0
       grind)
    | exact superpose eq89141 eq1347
    | (have j0 := eq1347 x y
       have j1 := eq89141 (σ y)
       grind)
    | exact resolve eq1347 eq89141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1347 eq89141
  have eq89322 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq89320 (σ y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89320
  have eq89326 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq89322 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq89322
    | (have j0 := eq89322 (σ y)
       grind)
    | exact resolve eq89322 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89322
  have eq89343 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq89326 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq89326
    | (have j0 := eq89326 (σ y)
       grind)
    | exact resolve eq89326 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89326
  have eq89358 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq26 eq89343
    | (have j0 := eq89343 (σ y)
       grind)
    | exact resolve eq89343 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89343
  have eq89372 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq80949 eq89358
    | (have j0 := eq89358 (σ y)
       grind)
    | exact resolve eq89358 eq80949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89358
  have eq89381 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have j0 := eq89372 (σ y)
       grind)
    | (have r₁ := eq89372 X0
       have r₂ := eq27
       grind)
    | exact resolve eq89372 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89372
  have eq89387 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq89381 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq89381
    | (have j0 := eq89381 (σ y)
       grind)
    | exact resolve eq89381 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89381
  have eq89393 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have j0 := eq89387 (σ y)
       have j1 := eq50119 x (σ y)
       grind)
    | (have r₁ := eq89387 x
       have r₂ := eq50119 (σ y) x
       grind)
    | (have r₁ := eq89387 x
       have r₂ := eq50119 x x
       grind)
    | exact resolve eq89387 eq50119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50119 eq89387
  have eq89411 : ∀ X0 : G, (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq89393
       have i₂ := eq241 sF3 x
       grind)
    | (have i₁ := eq89393
       have i₂ := eq241 X0 sF3
       grind)
    | exact superpose eq241 eq89393
    | exact resolve eq89393 eq241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq89393
  have eq90026 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52 sF4
       have i₂ := eq89411 sF4
       grind)
    | exact superpose eq89411 eq52
    | exact resolve eq52 eq89411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq90070 : (τ (σ y)) = (M.op y y) := by
    first
    | (have i₁ := eq10378
       have i₂ := eq89411 sF3
       grind)
    | exact superpose eq89411 eq10378
    | exact resolve eq10378 eq89411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10378
  have eq90103 : (σ y) = (τ (σ y)) := by
    first
    | (have i₁ := eq90070
       have i₂ := eq89411 y
       grind)
    | exact superpose eq89411 eq90070
    | exact resolve eq90070 eq89411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90070
  have eq90141 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq90026
    | exact resolve eq90026 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq90026
  have eq90500 : y = (σ y) := by
    first
    | exact superpose eq29 eq90103
    | exact resolve eq90103 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq90103
  have eq90700 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq90141 eq27
    | exact resolve eq27 eq90141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq90141
  have eq90783 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq90500 eq90700
    | exact resolve eq90700 eq90500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90700
  have eq92310 : ∀ X0 X2 : G, (σ y) = (M.op X2 (σ (k X0 X0))) ∨ (σ X0) = (M.op X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq7083 X0 x X2
       have i₂ := eq89411 x
       grind)
    | exact superpose eq89411 eq7083
    | (have j0 := eq7083 X0 x X2
       grind)
    | exact resolve eq7083 eq89411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7083
  have eq92311 : ∀ X0 X2 : G, y = (M.op X2 (σ (k X0 X0))) ∨ (σ X0) = (M.op X2 X2) := by
    intro X0 X2
    first
    | exact superpose eq90500 eq92310
    | (have j0 := eq92310 X0 X2
       grind)
    | exact resolve eq92310 eq90500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92310
  have eq92312 : ∀ X0 X2 : G, (σ X0) = (σ y) ∨ y = (M.op X2 (σ (k X0 X0))) := by
    intro X0 X2
    first
    | (have i₁ := eq92311 X0 X2
       have i₂ := eq89411 X2
       grind)
    | exact superpose eq89411 eq92311
    | (have j0 := eq92311 X0 X2
       grind)
    | exact resolve eq92311 eq89411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92311
  have eq92313 : ∀ X0 X2 : G, y = (M.op X2 (σ (k X0 X0))) ∨ (σ X0) = y := by
    intro X0 X2
    first
    | exact superpose eq90500 eq92312
    | (have j0 := eq92312 X0 X2
       grind)
    | exact resolve eq92312 eq90500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92312
  have eq92372 : ∀ X0 : G, y = (M.op X0 (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq134 eq92313
    | (have j0 := eq92313 (M.op x y) x
       grind)
    | exact resolve eq92313 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq92313
  have eq93005 : ∀ X0 : G, y = (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq19159 eq92372
    | exact resolve eq92372 eq19159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19159 eq92372
  have eq93313 : ∀ X0 : G, y = (M.op X0 (σ y)) ∨ y = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq93005 X0
       have i₂ := eq89411 sF1
       grind)
    | exact superpose eq89411 eq93005
    | exact resolve eq93005 eq89411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89411 eq93005
  have eq93510 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq90500 eq93313
    | exact resolve eq93313 eq90500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93313
  have eq93643 : ∀ X0 : G, y = (σ (M.op x y)) ∨ y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq20 eq93510
    | (have j0 := eq93510 X0
       grind)
    | exact resolve eq93510 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq93510
  have eq93731 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq93643 X0
       grind)
    | (have r₁ := eq93643 X0
       have r₂ := eq90783
       grind)
    | exact resolve eq93643 eq90783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93643
  have eq93983 : y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq93731 x
       grind)
    | exact superpose eq93731 eq18
    | (have j1 := eq93731 x
       grind)
    | exact resolve eq18 eq93731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq93731
  have eq93999 : x = y := by
    first
    | exact superpose eq80785 eq93983
    | exact resolve eq93983 eq80785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80785 eq93983
  have eq94310 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq93999
       grind)
    | exact superpose eq93999 eq24
    | exact resolve eq24 eq93999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq93999
  have eq94434 : y = (σ x) := by
    first
    | exact superpose eq90500 eq94310
    | exact resolve eq94310 eq90500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90500 eq94310
  have eq94492 : y = (σ x) := by
    first
    | (have i₁ := eq94434
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq94434
    | exact resolve eq94434 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq94434
  have eq94548 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq80949 eq94492
    | exact resolve eq94492 eq80949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80949 eq94492
  have eq94601 : False := by grind
  exact eq94601
