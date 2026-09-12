import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_y_pxx_pyy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) := by
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
  have eq30 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15
    | (have j0 := eq15 X0 x
       grind)
    | exact resolve eq15 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y)
       grind)
    | exact resolve eq10 eq20
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op (M.op x y) X0) := by
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
  have eq57 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X2 X2
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq9
    | (have j0 := eq9 X0 (σ x) (σ y)
       grind)
    | exact resolve eq9 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq30 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq30
    | (have j0 := eq30 y
       grind)
    | exact resolve eq30 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq81 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op x X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 x X1
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) x
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq9
    | exact resolve eq9 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq86 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (σ x) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq58 eq9
    | exact resolve eq9 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X0 X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x X0 X1
       have i₂ := eq81 X0 x
       grind)
    | exact superpose eq81 eq9
    | exact resolve eq9 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq94 : (M.op (M.op (σ x) (σ y)) x) = (M.op (M.op x y) (σ x)) := by
    first
    | (have i₁ := eq58 x
       have i₂ := eq81 sF2 x
       grind)
    | exact superpose eq81 eq58
    | exact resolve eq58 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq108 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X0 X1) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq86 eq9
    | exact resolve eq9 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq119 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op (M.op x y) X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq92 (M.op X0 X1) x
       have i₂ := eq92 X0 X1
       grind)
    | (have i₁ := eq92 (M.op x y) X0
       have i₂ := eq92 X0 X1
       grind)
    | exact superpose eq92 eq92
    | exact resolve eq92 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq119 sF0 X1
       have i₂ := eq9 sF0 x x
       grind)
    | (have i₁ := eq119 x X1
       have i₂ := eq9 x sF0 x
       grind)
    | exact superpose eq9 eq119
    | exact resolve eq119 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq139 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq134 X0 X1
       have i₂ := eq81 sF0 x
       grind)
    | exact superpose eq81 eq134
    | exact resolve eq134 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq153 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq153 (σ X0)
       grind)
    | exact superpose eq153 eq15
    | exact resolve eq15 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq178 X0
       have i₂ := eq153 X0
       grind)
    | exact superpose eq153 eq178
    | exact resolve eq178 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq178
  have eq200 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) (σ x)) (σ x)) := by
    first
    | exact superpose eq94 eq108
    | exact resolve eq108 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : (M.op (M.op (M.op x y) (M.op x y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq200
       have i₂ := eq57 sF0 sF2 sF2
       grind)
    | exact superpose eq57 eq200
    | exact resolve eq200 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq221 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq108 eq213
    | exact resolve eq213 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213
  have eq236 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X0) = (M.op (M.op X0 X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq221 eq9
    | exact resolve eq9 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : ∀ X0 : G, (M.op (σ (M.op x X0)) (σ (M.op x X0))) = (σ (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq179 (M.op x X0)
       have i₂ := eq81 (M.op x X0) X0
       grind)
    | (have i₁ := eq179 (M.op x y)
       have i₂ := eq81 (M.op x y) x
       grind)
    | exact superpose eq81 eq179
    | exact resolve eq179 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq10
    | exact resolve eq10 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq139 eq331
    | exact resolve eq331 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139 eq331
  have eq347 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
    intro X0
    first
    | (have i₁ := eq345 X0
       have i₂ := eq179 sF0
       grind)
    | exact superpose eq179 eq345
    | exact resolve eq345 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq348 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x X0)) (σ (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq20 eq347
    | (have j0 := eq347 X0
       grind)
    | exact resolve eq347 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq382 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq334 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq334
    | exact resolve eq334 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq454 : (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (τ (M.op (M.op (σ x) (σ y)) (M.op x y))) := by
    first
    | exact superpose eq221 eq382
    | exact resolve eq382 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq490 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq61
       have i₂ := eq14 sF3 sF2
       grind)
    | exact superpose eq14 eq61
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq61 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq494 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq490
    | exact resolve eq490 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq496 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq494
    | exact resolve eq494 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494
  have eq498 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq496
    | exact resolve eq496 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq496
  have eq528 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op (σ x) (σ y)) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq108 eq52
    | exact resolve eq52 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op (M.op x y) (σ x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq94 eq52
    | exact resolve eq52 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq563 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 X2 X3
       have i₂ := eq52 X0 X0 X2 X1
       grind)
    | (have i₁ := eq9 X0 X2 X3
       have i₂ := eq52 X0 X1 X2 X0
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 X4) (M.op X0 X2)) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X2) X3 X4
       have i₂ := eq52 X0 X2 (M.op X0 X2) X1
       grind)
    | (have i₁ := eq9 (M.op X0 X2) X3 X4
       have i₂ := eq52 X0 X1 (M.op X0 X2) X2
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq584 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X1) = (M.op (M.op (M.op x y) (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq535 X0 x
       have i₂ := eq57 sF0 sF2 x
       grind)
    | exact superpose eq57 eq535
    | exact resolve eq535 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq590 : ∀ X0 X2 X3 X4 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) X3) = (M.op (M.op X3 X4) (M.op X0 X2)) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq572 X0 x X2 X3 X4
       have i₂ := eq528 X0 x (M.op X0 X2) X3
       grind)
    | (have i₁ := eq572 (σ x) (σ y) X2 X3 X4
       have i₂ := eq528 (M.op (σ x) X2) x X2 X3
       grind)
    | exact superpose eq528 eq572
    | exact resolve eq572 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528 eq572
  have eq612 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = (M.op (M.op X0 X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq584 eq236
    | exact resolve eq236 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236
  have eq614 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X3 X4) (M.op X0 X2)) = (M.op (M.op (M.op x y) (M.op x y)) X3) := by
    intro X0 X2 X3 X4
    first
    | exact superpose eq584 eq590
    | exact resolve eq590 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq590
  have eq1151 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) X2) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq612 eq52
    | exact resolve eq52 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq2116 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) = (σ (M.op (M.op (M.op x y) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq179 (M.op X0 X0)
       have i₂ := eq83 X0 X0
       grind)
    | exact superpose eq83 eq179
    | exact resolve eq179 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq2222 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) = (σ (M.op (M.op (M.op x y) X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq2116 X0
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq2116
    | exact resolve eq2116 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2116
  have eq2286 : ∀ X0 : G, (σ (M.op (M.op (M.op x y) X0) X0)) = (M.op (M.op (M.op x y) (M.op x y)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2222 X0
       have i₂ := eq614 (σ X0) (σ X0) (σ X0) (σ X0)
       grind)
    | exact superpose eq614 eq2222
    | exact resolve eq2222 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2222
  have eq2778 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) = (τ (M.op (M.op (M.op x y) (M.op x y)) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq382 (M.op X0 X1)
       have i₂ := eq614 X0 X1 X0 X1
       grind)
    | (have i₁ := eq382 (M.op (M.op x y) (M.op x y))
       have i₂ := eq614 X0 x (M.op (M.op x y) (M.op x y)) x
       grind)
    | exact superpose eq614 eq382
    | exact resolve eq382 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2804 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op x y) X4) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq614 eq52
    | exact resolve eq52 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3148 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq348 x
       have i₂ := eq179 x
       grind)
    | exact superpose eq179 eq348
    | exact resolve eq348 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq3186 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (M.op x y) (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq3148
       have i₂ := eq614 (σ x) (σ x) (σ x) (σ x)
       grind)
    | exact superpose eq614 eq3148
    | exact resolve eq3148 eq614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614 eq3148
  have eq3197 : (M.op (M.op (M.op x y) (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3186
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3186
    | exact resolve eq3186 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3186
  have eq3203 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq108 eq3197
    | exact resolve eq3197 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3197
  have eq3215 : (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq3203 eq454
    | exact resolve eq454 eq3203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq454 eq3203
  have eq3231 : (M.op (τ (σ (M.op x y))) (τ (σ (M.op x y)))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq3215
       have i₂ := eq382 sF1
       grind)
    | exact superpose eq382 eq3215
    | exact resolve eq3215 eq382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3215
  have eq3237 : (M.op (M.op x y) (M.op x y)) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq37 eq3231
    | exact resolve eq3231 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq3231
  have eq3500 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = (M.op (M.op X0 X1) (τ (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq3237 eq563
    | exact resolve eq563 eq3237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7115 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op (σ x) (σ y))) = (M.op (M.op X0 X1) (τ (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3500 eq1151
    | exact resolve eq1151 eq3500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151
  have eq7121 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X2) X0) = (M.op (M.op X0 X1) (τ (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq3500 eq52
    | exact resolve eq52 eq3500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq3500
  have eq11554 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x y)) (σ X0)) = (σ (M.op (M.op X0 X1) (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2286 x
       have i₂ := eq563 sF0 x x x
       grind)
    | (have i₁ := eq2286 X0
       have i₂ := eq563 X0 X1 sF0 X0
       grind)
    | exact superpose eq563 eq2286
    | exact resolve eq2286 eq563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq11582 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) X0) = (τ (M.op (M.op (M.op x y) (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq2286 eq10
    | exact resolve eq10 eq2286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2286
  have eq18637 : ∀ X0 X1 X2 : G, (M.op (τ (M.op X1 X2)) (τ (M.op X1 X2))) = (τ (M.op (M.op (M.op x y) X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq382 (M.op X1 X2)
       have i₂ := eq2804 X1 X2 X1 X2 X0
       grind)
    | (have i₁ := eq382 (M.op (M.op x y) x)
       have i₂ := eq2804 (M.op (M.op x y) x) X1 X2 x x
       grind)
    | exact superpose eq2804 eq382
    | exact resolve eq382 eq2804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq2804
  have eq22438 : ∀ X0 : G, (τ (M.op (M.op (M.op x y) (M.op x y)) X0)) = (M.op (M.op (M.op x y) (τ X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq11582 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11582
    | exact resolve eq11582 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11582
  have eq22494 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) (τ X0)) = (τ (M.op (M.op (M.op x y) (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq22438 X0
       have i₂ := eq57 sF0 (τ X0) (τ X0)
       grind)
    | exact superpose eq57 eq22438
    | exact resolve eq22438 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq22438
  have eq22518 : ∀ X0 X1 : G, (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) = (M.op (M.op (M.op x y) (M.op x y)) (τ X0)) := by
    intro X0 X1
    first
    | exact superpose eq22494 eq2778
    | exact resolve eq2778 eq22494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2778 eq22494
  have eq22551 : ∀ X0 X1 : G, (τ (M.op (M.op (M.op x y) X0) X1)) = (M.op (M.op (M.op x y) (M.op x y)) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18637 X0 X1 x
       have i₂ := eq22518 X1 x
       grind)
    | exact superpose eq22518 eq18637
    | exact resolve eq18637 eq22518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18637 eq22518
  have eq59122 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq498
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq498
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq498 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59155 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq59122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59122
    | exact resolve eq59122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59122
  have eq59164 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq59155
    | exact resolve eq59155 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59155
  have eq59165 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq59164
       have r₂ := eq27
       grind)
    | exact resolve eq59164 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59164
  have eq59166 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq59165
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59165
    | exact resolve eq59165 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59165
  have eq59167 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq59166
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq59166
    | exact resolve eq59166 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59166
  have eq59175 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq59167 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq59167
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq59167
       grind)
    | exact resolve eq12 eq59167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59167
  have eq63121 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq59175
    | (have j0 := eq59175 (σ x)
       grind)
    | (have r₁ := eq59175 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq59175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59175
  have eq63127 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq63121
  have eq63133 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq61 eq63127
    | exact resolve eq63127 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq63127
  have eq63144 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq63133
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq63133
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq63133 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63133
  have eq63177 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq63144
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq63144
    | exact resolve eq63144 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63144
  have eq63186 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq63177
    | exact resolve eq63177 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63177
  have eq63187 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq63186
       have r₂ := eq27
       grind)
    | exact resolve eq63186 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63186
  have eq63188 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq63187
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq63187
    | exact resolve eq63187 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63187
  have eq63189 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq63188
  have eq63190 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq63189
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq63189
    | exact resolve eq63189 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63189
  have eq63191 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq63190
  have eq63193 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12 y x
       have i₂ := eq63191
       grind)
    | exact superpose eq63191 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq63191
       grind)
    | exact resolve eq12 eq63191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63197 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq179 y
       have i₂ := eq63191
       grind)
    | exact superpose eq63191 eq179
    | exact resolve eq179 eq63191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq63191
  have eq63325 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq63197
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq63197
    | exact resolve eq63197 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63197
  have eq63352 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq63325
    | exact resolve eq63325 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63325
  have eq71760 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq63193 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq63193
    | (have j0 := eq63193 x
       grind)
    | (have r₁ := eq63193 x
       have r₂ := eq18
       grind)
    | exact resolve eq63193 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63193
  have eq71770 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq71760
  have eq72016 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq498
       have i₂ := eq71770
       grind)
    | exact superpose eq71770 eq498
    | exact resolve eq498 eq71770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498 eq71770
  have eq72022 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq72016
  have eq72027 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq72022
    | exact resolve eq72022 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72022
  have eq72031 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq72027
       have r₂ := eq27
       grind)
    | exact resolve eq72027 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72027
  have eq72063 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq72031 eq63352
    | exact resolve eq63352 eq72031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63352 eq72031
  have eq72166 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq72063
  have eq72231 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq72166
       have r₂ := eq27
       grind)
    | exact resolve eq72166 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72166
  have eq72287 : (M.op (M.op x y) (M.op x y)) = (M.op (τ (σ x)) (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq72231 eq3237
    | exact resolve eq3237 eq72231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3237
  have eq72299 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ x)) = (M.op (M.op X0 X2) (τ (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq72231 eq7115
    | exact resolve eq7115 eq72231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7115
  have eq72300 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op X1 X2) (τ (σ x))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq72231 eq7121
    | exact resolve eq7121 eq72231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7121
  have eq72336 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op X1 X2) x) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq38 eq72300
    | exact resolve eq72300 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72300
  have eq72337 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ x)) = (M.op (M.op X0 X2) x) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq38 eq72299
    | exact resolve eq72299 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72299
  have eq72347 : (M.op x x) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq72287
    | exact resolve eq72287 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72287
  have eq72361 : ∀ X0 X1 : G, (M.op (M.op x y) X1) = (M.op (M.op (M.op x y) X0) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq72336 X0 X1 x
       have i₂ := eq92 X1 x
       grind)
    | (have i₁ := eq72336 X0 x y
       have i₂ := eq92 x X1
       grind)
    | exact superpose eq92 eq72336
    | exact resolve eq72336 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72336
  have eq72362 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X0 X1) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq72337 X0 X1 x
       have i₂ := eq92 X0 x
       grind)
    | (have i₁ := eq72337 x X1 y
       have i₂ := eq92 x X1
       grind)
    | exact superpose eq92 eq72337
    | exact resolve eq72337 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72337
  have eq72368 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq108 eq72362
    | exact resolve eq72362 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq72362
  have eq74242 : ∀ X0 : G, (M.op (M.op x x) (τ X0)) = (τ (M.op (M.op x x) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq72347 eq22551
    | exact resolve eq22551 eq72347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22551 eq72347
  have eq74434 : ∀ X0 : G, (τ (M.op (M.op x y) X0)) = (M.op (M.op x x) (τ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq74242 X0
       have i₂ := eq81 X0 x
       grind)
    | exact superpose eq81 eq74242
    | exact resolve eq74242 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74242
  have eq74517 : ∀ X0 : G, (τ (M.op (M.op x y) X0)) = (M.op (M.op x y) (τ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq74434 X0
       have i₂ := eq81 (τ X0) x
       grind)
    | exact superpose eq81 eq74434
    | exact resolve eq74434 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74434
  have eq74576 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq72231 eq72368
    | exact resolve eq72368 eq72231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72368
  have eq74737 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq74576 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74576
  have eq76465 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq74737 eq26
    | (have j1 := eq74737 (σ y)
       grind)
    | exact resolve eq26 eq74737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74737
  have eq97299 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (τ (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq76465 eq74517
    | exact resolve eq74517 eq76465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74517 eq76465
  have eq97341 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) (τ (σ y))) ∨ x = (M.op x y) := by grind
  clear eq97299
  have eq97366 : (τ (M.op (σ x) (σ y))) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq39 eq97341
    | exact resolve eq97341 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq97341
  have eq97423 : (τ (σ x)) = (M.op (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq72231 eq97366
    | exact resolve eq97366 eq72231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72231 eq97366
  have eq97471 : (τ (σ x)) = (M.op (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq97423
  have eq97473 : x = (M.op (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq38 eq97471
    | exact resolve eq97471 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq97471
  have eq97504 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq97473 eq72361
    | exact resolve eq72361 eq97473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72361
  have eq97616 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq97504 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97504
  have eq100192 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq97616 eq97473
    | exact resolve eq97473 eq97616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97473 eq97616
  have eq100378 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq100192
  have eq100541 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq100378
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq100378
    | exact resolve eq100378 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100378
  have eq100542 : x = (M.op x y) := by grind
  clear eq100541
  have eq100678 : x = (M.op x y) := by
    first
    | exact superpose eq100542 eq18
    | exact resolve eq18 eq100542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq100679 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq100542 eq20
    | exact resolve eq20 eq100542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq100687 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq100542 eq81
    | exact resolve eq81 eq100542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq100688 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X0 X1) x) := by
    intro X0 X1
    first
    | exact superpose eq100542 eq92
    | exact resolve eq92 eq100542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq100946 : ∀ X0 X1 : G, (M.op (M.op x x) (σ X0)) = (σ (M.op (M.op X0 X1) x)) := by
    intro X0 X1
    first
    | exact superpose eq100542 eq11554
    | exact resolve eq11554 eq100542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11554 eq100542
  have eq103111 : ∀ X0 : G, (σ (M.op x X0)) = (M.op (M.op x x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq100946 X0 x
       have i₂ := eq100688 X0 x
       grind)
    | exact superpose eq100688 eq100946
    | exact resolve eq100946 eq100688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100688 eq100946
  have eq103482 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq100679
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq100679
    | exact resolve eq100679 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100679
  have eq104264 : ∀ X0 : G, (σ (M.op x X0)) = (M.op x (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq103111 X0
       have i₂ := eq100687 (σ X0) x
       grind)
    | exact superpose eq100687 eq103111
    | exact resolve eq103111 eq100687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103111
  have eq104579 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq103482 eq22
    | exact resolve eq22 eq103482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq104580 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq103482 eq26
    | exact resolve eq26 eq103482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq103482
  have eq108065 : (σ x) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq104264 y
       have i₂ := eq100678
       grind)
    | exact superpose eq100678 eq104264
    | exact resolve eq104264 eq100678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100678 eq104264
  have eq108113 : (σ x) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq108065
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq108065
    | exact resolve eq108065 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq108065
  have eq108130 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq108113
       have i₂ := eq104579
       grind)
    | exact superpose eq104579 eq108113
    | exact resolve eq108113 eq104579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104579 eq108113
  have eq108179 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq108130 eq100687
    | exact resolve eq100687 eq108130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100687
  have eq108252 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq108179 eq104580
    | exact resolve eq104580 eq108179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104580 eq108179
  have eq108259 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq108130 eq108252
    | exact resolve eq108252 eq108130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108130 eq108252
  have eq108308 : False := by grind
  exact eq108308

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxx_pxx_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
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
  have eq63 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq63 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq63
    | exact resolve eq63 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq64
    | exact resolve eq64 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq64
  have eq102 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq102 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq717 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq108 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq721 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq717 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq717 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq717 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq717 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq717 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq723 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq721 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq721
    | (have j0 := eq721 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq721 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq727 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq721 (τ X0) X1
       grind)
    | exact superpose eq721 eq18
    | (have j1 := eq721 (k X0 (σ X1)) (σ (M.op X1 (τ X0)))
       grind)
    | exact resolve eq18 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq721
  have eq1024 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq727 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq727
    | exact resolve eq727 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq1054 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1024 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1024
    | (have j0 := eq1024 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq1024 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1024
  have eq10978 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq723 y x
       grind)
    | exact superpose eq723 eq16
    | (have j1 := eq723 x y
       grind)
    | exact resolve eq16 eq723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq11035 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq10978
       have i₂ := eq1054 y x
       grind)
    | exact superpose eq1054 eq10978
    | (have j1 := eq1054 (σ x) (σ y)
       grind)
    | (have r₁ := eq10978
       have r₂ := eq1054 y x
       grind)
    | (have r₁ := eq10978
       have r₂ := eq1054 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq10978
       have r₂ := eq1054 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq10978 eq1054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1054 eq10978
  have eq11036 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq11035
  have eq11040 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq11036
       grind)
    | exact superpose eq11036 eq10
    | exact resolve eq10 eq11036
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11036
  have eq11081 : x = y ∨ x = y := by
    first
    | (have i₁ := eq11040
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11040
    | exact resolve eq11040 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11040
  have eq11082 : x = y := by grind
  clear eq11081
  have eq11084 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11082
       grind)
    | exact superpose eq11082 eq16
    | exact resolve eq16 eq11082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11082
  have eq11085 : False := by grind
  exact eq11085

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_pyx_pyx_pxx_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq27 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq73 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq67 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq75 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq74 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq76 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq73 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq73 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq73 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq80 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq75 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq75 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq75 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq75 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq207 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq76 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq76
    | (have j0 := eq76 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq76 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq76 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq76 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq214 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq207 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq217 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq214 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq214 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq214 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq214 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq219 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq217 X0 X1
       have i₂ := eq27 X1
       grind)
    | exact superpose eq27 eq217
    | (have j0 := eq217 X0 X1
       grind)
    | exact resolve eq217 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq217
  have eq247 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq251 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq247 X0 X1
       have j1 := eq219 X1 X0
       grind)
    | (have r₁ := eq247 X1 X0
       have r₂ := eq219 X0 X1
       grind)
    | (have r₁ := eq247 X1 X1
       have r₂ := eq219 X1 X1
       grind)
    | exact resolve eq247 eq219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219 eq247
  have eq355 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq251 (σ X1) (σ X0)
       grind)
    | exact superpose eq251 eq15
    | exact resolve eq15 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq355 X0 X1
       have i₂ := eq251 X1 X0
       grind)
    | exact superpose eq251 eq355
    | exact resolve eq355 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq355
  have eq362 : False := by grind
  exact eq362

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pyx_pxx_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq35 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (τ X1) (τ X1)) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq42 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq51 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
    | (have r₁ := eq14 (M.op X0 X0) (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq51
    | (have j0 := eq51 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq51 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (τ X0) = (τ X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq51 (τ X1) (τ X0)
       grind)
    | exact superpose eq51 eq42
    | (have j1 := eq51 (τ X0) (τ X1)
       grind)
    | exact resolve eq42 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq51
  have eq297 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65 y x
       grind)
    | exact superpose eq65 eq16
    | (have j1 := eq65 x y
       grind)
    | exact resolve eq16 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq432 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq38 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq611 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq40 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq612 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq611 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq611
    | exact resolve eq611 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq616 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq612 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq612
    | exact resolve eq612 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq642 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq616 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq616
    | exact resolve eq616 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq704 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq432 X0
       have i₂ := eq642 X0
       grind)
    | exact superpose eq642 eq432
    | exact resolve eq432 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432 eq642
  have eq6178 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1
       have i₂ := eq77 X0 X1
       grind)
    | (have i₁ := eq11 X0
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq11
    | (have j1 := eq77 X0 X1
       grind)
    | exact resolve eq11 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq6232 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6178 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6178
    | (have j0 := eq6178 X0 X1
       grind)
    | exact resolve eq6178 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6178
  have eq6276 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6232 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6232
    | (have j0 := eq6232 (τ (k (σ X0) X1)) (M.op (τ X1) X0)
       grind)
    | exact resolve eq6232 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6232
  have eq6318 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6276 X0 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq6276
    | (have j0 := eq6276 X0 X1
       grind)
    | exact resolve eq6276 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq6276
  have eq6324 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6318 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6318
    | (have j0 := eq6318 X0 (σ X1)
       grind)
    | exact resolve eq6318 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6318
  have eq6421 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq297
       have i₂ := eq6324 x y
       grind)
    | exact superpose eq6324 eq297
    | (have j1 := eq6324 x y
       grind)
    | (have r₁ := eq297
       have r₂ := eq6324 (M.op x y) (k y x)
       grind)
    | (have r₁ := eq297
       have r₂ := eq6324 (k y x) (M.op x y)
       grind)
    | exact resolve eq297 eq6324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq6324
  have eq6422 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq6421
  have eq6423 : (σ x) = (σ y) := by grind
  clear eq6422
  have eq6463 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6423
       grind)
    | exact superpose eq6423 eq10
    | exact resolve eq10 eq6423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6423
  have eq6504 : x = y := by
    first
    | (have i₁ := eq6463
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6463
    | exact resolve eq6463 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6463
  have eq6508 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6504
       grind)
    | exact superpose eq6504 eq16
    | exact resolve eq16 eq6504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6504
  have eq6509 : False := by grind
  exact eq6509

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pyx_x_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq35 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (τ X1) (τ X1)) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 X0 (τ X1)
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq42 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq51 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
    | (have r₁ := eq14 (M.op X0 X0) (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq51
    | (have j0 := eq51 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq51 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (τ X0) = (τ X1) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq42 X0 X1
       have i₂ := eq51 (τ X1) (τ X0)
       grind)
    | exact superpose eq51 eq42
    | (have j1 := eq51 (τ X0) (τ X1)
       grind)
    | exact resolve eq42 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq51
  have eq297 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65 y x
       grind)
    | exact superpose eq65 eq16
    | (have j1 := eq65 x y
       grind)
    | exact resolve eq16 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq432 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq38 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq611 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq40 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq612 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq611 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq611
    | exact resolve eq611 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq616 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq612 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq612
    | exact resolve eq612 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq642 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq616 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq616
    | exact resolve eq616 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq704 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq432 X0
       have i₂ := eq642 X0
       grind)
    | exact superpose eq642 eq432
    | exact resolve eq432 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq432 eq642
  have eq6178 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 X1
       have i₂ := eq77 X0 X1
       grind)
    | (have i₁ := eq11 X0
       have i₂ := eq77 X0 X1
       grind)
    | exact superpose eq77 eq11
    | (have j1 := eq77 X0 X1
       grind)
    | exact resolve eq11 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq6232 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6178 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6178
    | (have j0 := eq6178 X0 X1
       grind)
    | exact resolve eq6178 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6178
  have eq6276 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6232 X1 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6232
    | (have j0 := eq6232 (τ (k (σ X0) X1)) (M.op (τ X1) X0)
       grind)
    | exact resolve eq6232 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6232
  have eq6318 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq6276 X0 X1
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq6276
    | (have j0 := eq6276 X0 X1
       grind)
    | exact resolve eq6276 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq6276
  have eq6324 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6318 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6318
    | (have j0 := eq6318 X0 (σ X1)
       grind)
    | exact resolve eq6318 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6318
  have eq6421 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq297
       have i₂ := eq6324 x y
       grind)
    | exact superpose eq6324 eq297
    | (have j1 := eq6324 x y
       grind)
    | (have r₁ := eq297
       have r₂ := eq6324 (M.op x y) (k y x)
       grind)
    | (have r₁ := eq297
       have r₂ := eq6324 (k y x) (M.op x y)
       grind)
    | exact resolve eq297 eq6324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297 eq6324
  have eq6422 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq6421
  have eq6423 : (σ x) = (σ y) := by grind
  clear eq6422
  have eq6463 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6423
       grind)
    | exact superpose eq6423 eq10
    | exact resolve eq10 eq6423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6423
  have eq6504 : x = y := by
    first
    | (have i₁ := eq6463
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6463
    | exact resolve eq6463 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6463
  have eq6508 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6504
       grind)
    | exact superpose eq6504 eq16
    | exact resolve eq16 eq6504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6504
  have eq6509 : False := by grind
  exact eq6509

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_y_pyx_pxx_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
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
  have eq67 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X2 X2) X4) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X2 X2) X0 X3 X4
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq52 (M.op X1 X2) X0 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X3) X5) X4) = (M.op (M.op (M.op X0 X1) X2) X4) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq52 (M.op X0 X1) X5 X4 X2
       have i₂ := eq52 X0 X1 X5 X3
       grind)
    | (have i₁ := eq52 (M.op X0 X1) X5 X4 X2
       have i₂ := eq52 X0 X3 X5 X1
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X4) X3) = (M.op (M.op (M.op X0 X0) X1) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq52 (M.op X1 X2) X0 X3 X4
       have i₂ := eq9 X0 X1 X2
       grind)
    | (have i₁ := eq52 (M.op X0 X0) X1 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X2 X2 X0 X3
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq52 X1 X2 X0 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op X3 X3) (M.op X0 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 X3 (M.op X0 X4) X2
       have i₂ := eq52 X0 X4 X2 X1
       grind)
    | (have i₁ := eq9 X3 (M.op X0 X4) X2
       have i₂ := eq52 X0 X1 X2 X4
       grind)
    | exact superpose eq52 eq9
    | exact resolve eq9 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X0 X1) X2) X4) = (M.op (M.op X4 X5) (M.op X2 X3)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq71 (M.op X2 X3) X0 X4 X5
       have i₂ := eq71 X2 X3 X0 X1
       grind)
    | (have i₁ := eq71 (M.op X2 X3) X0 X4 X5
       have i₂ := eq71 X0 X1 X2 X3
       grind)
    | exact superpose eq71 eq71
    | exact resolve eq71 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131 : ∀ X0 X1 X2 : G, (M.op X2 X2) ≠ (M.op (M.op X0 X1) X2) ∨ (k (M.op X2 X2) X0) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X2 X2) X0
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq12 (M.op X1 X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X2 X2) X0
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 X2) (M.op X1 X2)) X1
       have r₂ := eq9 (M.op X1 X2) X1 X2
       grind)
    | (have r₁ := eq12 (M.op (M.op X0 X0) (M.op X0 X0)) X0
       have r₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op X4 X4) X5) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq67 X2 X3 X4 X0 X5
       have i₂ := eq71 (M.op X2 X3) X4 X0 X1
       grind)
    | (have i₁ := eq67 X2 X3 X4 X0 X5
       have i₂ := eq71 X0 X1 (M.op X2 X3) X4
       grind)
    | exact superpose eq71 eq67
    | exact resolve eq67 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq642 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq643 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq642 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq642
    | (have j0 := eq642 X0 (σ X1)
       grind)
    | exact resolve eq642 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq735 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X4 X5) X6) X3) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq70 X4 X0 X1 X3 X2
       have i₂ := eq68 X4 X5 X6 X4 X3 X0
       grind)
    | (have i₁ := eq70 X4 X0 X1 X3 X2
       have i₂ := eq68 X4 X4 X0 X5 X3 X6
       grind)
    | exact superpose eq68 eq70
    | exact resolve eq70 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq745 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op (M.op X3 X4) X5) X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq70 X2 X3 X4 X0 X5
       have i₂ := eq71 (M.op X2 X2) X3 X0 X1
       grind)
    | (have i₁ := eq70 X2 X3 X4 X0 X5
       have i₂ := eq71 X0 X1 (M.op X2 X2) X3
       grind)
    | exact superpose eq71 eq70
    | exact resolve eq70 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1049 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op X0 X0) (M.op X2 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq86 X2 X3 (M.op X2 X3) X0 X4
       have i₂ := eq9 (M.op X2 X3) X0 X1
       grind)
    | (have i₁ := eq86 X0 X1 X2 X0 X4
       have i₂ := eq9 X0 (M.op X0 X1) X2
       grind)
    | exact superpose eq9 eq86
    | exact resolve eq86 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq1708 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq643 y x
       grind)
    | exact superpose eq643 eq16
    | (have j1 := eq643 x x
       grind)
    | exact resolve eq16 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1739 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq643 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq2355 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X0 X1)) X0) = (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq131 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131
  have eq4435 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1739 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1739
    | (have j0 := eq1739 (τ X0)
       grind)
    | exact resolve eq1739 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4445 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4435 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4435
    | (have j0 := eq4435 X0
       grind)
    | exact resolve eq4435 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4435
  have eq4452 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4445 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4445
    | (have j0 := eq4445 X0
       grind)
    | exact resolve eq4445 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4445
  have eq13372 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1708
       have i₂ := eq642 y x
       grind)
    | exact superpose eq642 eq1708
    | (have j1 := eq642 x (σ x)
       grind)
    | exact resolve eq1708 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1708
  have eq13375 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq13372
  have eq13413 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq12 (σ x) (σ x)
       have i₂ := eq13375
       grind)
    | exact superpose eq13375 eq12
    | (have r₁ := eq12 (σ x) (σ x)
       have r₂ := eq13375
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq13375
       grind)
    | exact resolve eq12 eq13375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13375
  have eq13470 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq13413
  have eq13472 : (σ x) = (σ (k x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13470
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq13470
    | exact resolve eq13470 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13470
  have eq13478 : (k x x) = (τ (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq13472
       grind)
    | exact superpose eq13472 eq10
    | exact resolve eq10 eq13472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13472
  have eq13502 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13478
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq13478
    | exact resolve eq13478 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13478
  have eq13503 : x = (M.op x x) := by
    first
    | (have j1 := eq4452 x
       grind)
    | (have r₁ := eq13502
       have r₂ := eq4452 x
       grind)
    | exact resolve eq13502 eq4452
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4452 eq13502
  have eq13504 : ∀ X0 X1 : G, (M.op (M.op X0 X1) x) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 x X0 X1
       have i₂ := eq13503
       grind)
    | exact superpose eq13503 eq9
    | exact resolve eq9 eq13503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13505 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = X0 ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq13503
       grind)
    | exact superpose eq13503 eq13
    | (have j0 := eq13 X0 x
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq13503
       grind)
    | exact resolve eq13 eq13503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13540 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq13503
       grind)
    | exact superpose eq13503 eq12
    | (have r₁ := eq12 x x
       have r₂ := eq13503
       grind)
    | exact resolve eq12 eq13503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13541 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 x x X0 X1
       have i₂ := eq13503
       grind)
    | exact superpose eq13503 eq52
    | exact resolve eq52 eq13503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq13597 : x = (k x x) := by grind
  clear eq13540
  have eq13598 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq13505 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13505
  have eq13627 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1739 x
       have i₂ := eq13597
       grind)
    | exact superpose eq13597 eq1739
    | (have j0 := eq1739 x
       grind)
    | exact resolve eq1739 eq13597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1739
  have eq13632 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq13627
  have eq13769 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq13504 (M.op X0 X1) x
       have i₂ := eq13504 X0 X1
       grind)
    | exact superpose eq13504 eq13504
    | exact resolve eq13504 eq13504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13801 : (M.op x (σ x)) = (M.op (σ x) x) := by
    first
    | (have i₁ := eq13504 (σ x) (σ x)
       have i₂ := eq13632
       grind)
    | exact superpose eq13632 eq13504
    | exact resolve eq13504 eq13632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14049 : ∀ X0 X1 : G, (M.op x x) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13769 X0 X1
       have i₂ := eq13504 x X0
       grind)
    | exact superpose eq13504 eq13769
    | exact resolve eq13769 eq13504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13769
  have eq14140 : ∀ X0 X1 : G, x = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14049 X0 X1
       have i₂ := eq13503
       grind)
    | exact superpose eq13503 eq14049
    | exact resolve eq14049 eq13503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13503 eq14049
  have eq14272 : x = (M.op x (σ x)) := by
    first
    | (have i₁ := eq14140 (σ x) (σ x)
       have i₂ := eq13632
       grind)
    | exact superpose eq13632 eq14140
    | exact resolve eq14140 eq13632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14277 : ∀ X0 X1 : G, x ≠ x ∨ (M.op (M.op X0 X1) x) = (k x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 x (M.op X0 X1)
       have i₂ := eq14140 X0 X1
       grind)
    | exact superpose eq14140 eq12
    | (have j0 := eq12 x (M.op X0 X1)
       grind)
    | (have r₁ := eq12 x (M.op X0 X1)
       have r₂ := eq14140 X0 X1
       grind)
    | exact resolve eq12 eq14140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14338 : ∀ X0 X1 : G, (M.op (M.op X0 X1) x) = (k x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq14277 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14277
  have eq14377 : ∀ X0 X1 : G, (M.op x X0) = (k x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14338 X0 X1
       have i₂ := eq13504 X0 X1
       grind)
    | exact superpose eq13504 eq14338
    | exact resolve eq14338 eq13504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14338
  have eq14575 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op X0 X4)) = (M.op (M.op x X0) X2) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq92 x x X0 X4 X2 X3
       have i₂ := eq13541 X0 x
       grind)
    | exact superpose eq13541 eq92
    | exact resolve eq92 eq13541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq14588 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X3) X4) = (M.op (M.op x X0) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq735 X1 X2 X3 X4 x x X0
       have i₂ := eq13541 X0 x
       grind)
    | exact superpose eq13541 eq735
    | exact resolve eq735 eq13541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735
  have eq14589 : ∀ X0 X1 X2 X3 : G, (M.op (M.op x X0) X1) = (M.op (M.op X1 X2) (M.op X3 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq745 X1 X2 X3 x x X0
       have i₂ := eq13541 X0 x
       grind)
    | exact superpose eq13541 eq745
    | exact resolve eq745 eq13541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745
  have eq14809 : ∀ X1 X2 X3 : G, (M.op x X1) = (M.op (M.op X1 X2) (M.op X3 X3)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq14589 x X1 X2 X3
       have i₂ := eq13541 X1 x
       grind)
    | exact superpose eq13541 eq14589
    | exact resolve eq14589 eq13541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14589
  have eq14810 : ∀ X1 X2 X3 X4 : G, (M.op (M.op (M.op X1 X2) X3) X4) = (M.op x X4) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq14588 x X1 X2 X3 X4
       have i₂ := eq13541 X4 x
       grind)
    | exact superpose eq13541 eq14588
    | exact resolve eq14588 eq13541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14588
  have eq14823 : ∀ X0 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op X0 X4)) = (M.op x X2) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq14575 X0 X2 X3 X4
       have i₂ := eq13541 X2 X0
       grind)
    | exact superpose eq13541 eq14575
    | exact resolve eq14575 eq13541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13541 eq14575
  have eq15029 : x = (M.op (σ x) x) := by
    first
    | (have i₁ := eq13801
       have i₂ := eq14272
       grind)
    | exact superpose eq14272 eq13801
    | exact resolve eq13801 eq14272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13801 eq14272
  have eq15085 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ x)) (M.op X0 X2)) = (M.op x (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1049 (σ x) x X0 X1 X2
       have i₂ := eq15029
       grind)
    | exact superpose eq15029 eq1049
    | exact resolve eq1049 eq15029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049 eq15029
  have eq15093 : ∀ X0 X2 : G, x = (M.op (M.op (σ x) (σ x)) (M.op X0 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq15085 X0 x X2
       have i₂ := eq14140 X0 x
       grind)
    | exact superpose eq14140 eq15085
    | exact resolve eq15085 eq14140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15085
  have eq15143 : ∀ X0 X2 : G, x = (M.op (σ x) (M.op X0 X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq15093 X0 X2
       have i₂ := eq13632
       grind)
    | exact superpose eq13632 eq15093
    | exact resolve eq15093 eq13632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15093
  have eq15218 : x = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15143 (σ x) (σ x)
       have i₂ := eq13632
       grind)
    | exact superpose eq13632 eq15143
    | exact resolve eq15143 eq13632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15143
  have eq15355 : x = (σ x) := by
    first
    | (have i₁ := eq15218
       have i₂ := eq13632
       grind)
    | exact superpose eq13632 eq15218
    | exact resolve eq15218 eq13632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13632 eq15218
  have eq15551 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15355
       grind)
    | exact superpose eq15355 eq16
    | exact resolve eq16 eq15355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15560 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) x) := by
    intro X0
    first
    | (have i₁ := eq15 X0 x
       have i₂ := eq15355
       grind)
    | exact superpose eq15355 eq15
    | exact resolve eq15 eq15355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15562 : ∀ X0 : G, (k x (τ X0)) = (τ (k x X0)) := by
    intro X0
    first
    | (have i₁ := eq28 x X0
       have i₂ := eq15355
       grind)
    | exact superpose eq15355 eq28
    | exact resolve eq28 eq15355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq15902 : ∀ X0 X1 : G, (τ (M.op x X0)) = (k x (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15562 (M.op X0 X1)
       have i₂ := eq14377 X0 X1
       grind)
    | exact superpose eq14377 eq15562
    | exact resolve eq15562 eq14377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15562
  have eq17598 : ∀ X0 : G, (k (M.op x X0) X0) = (M.op X0 (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq2355 x x
       have i₂ := eq14809 x x x
       grind)
    | exact superpose eq14809 eq2355
    | exact resolve eq2355 eq14809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2355 eq14809
  have eq21261 : ∀ X0 : G, (k (τ (M.op x (σ X0))) X0) = (τ (M.op (σ X0) (M.op x (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq22 (M.op x (σ X0)) X0
       have i₂ := eq17598 (σ X0)
       grind)
    | exact superpose eq17598 eq22
    | exact resolve eq22 eq17598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq17598
  have eq25603 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X0) = (k (M.op X0 X1) x) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq71 (M.op X0 X1) X2 X0 X1
       have i₂ := eq13598 (M.op X0 X1)
       grind)
    | exact superpose eq13598 eq71
    | (have j1 := eq13598 (M.op X0 X1)
       grind)
    | exact resolve eq71 eq13598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq25651 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X2) (M.op X3 X4)) = (k (M.op (M.op X0 X0) X1) x) ∨ (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 X0) X1) x) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq410 (M.op (M.op X0 X0) X1) X2 X3 X4 X0 X1
       have i₂ := eq13598 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq13598 eq410
    | (have j1 := eq13598 (M.op (M.op X0 X0) X1)
       grind)
    | exact resolve eq410 eq13598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq25703 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X0) X1)) = (k (M.op (M.op X0 X0) X1) x) ∨ (M.op (M.op X0 X0) X1) = (M.op (M.op (M.op X0 X0) X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq25651 X0 X1 x x x
       have i₂ := eq14823 x (M.op (M.op X0 X0) X1) x x
       grind)
    | exact superpose eq14823 eq25651
    | (have j0 := eq25651 X0 X1 x x x
       grind)
    | exact resolve eq25651 eq14823
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14823 eq25651
  have eq25751 : ∀ X0 X1 : G, (M.op x X0) = (k (M.op X0 X1) x) ∨ (M.op X0 X1) = (M.op (M.op X0 X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq25603 X0 X1 x
       have i₂ := eq14810 X0 X1 x X0
       grind)
    | exact superpose eq14810 eq25603
    | (have j0 := eq25603 X0 X1 x
       grind)
    | exact resolve eq25603 eq14810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14810 eq25603
  have eq25966 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X0) X1)) = (k (M.op (M.op X0 X0) X1) x) := by
    intro X0 X1
    first
    | (have j0 := eq25703 X0 X1
       have j1 := eq12 (M.op (M.op X0 X0) X1) x
       grind)
    | (have r₁ := eq25703 X0 X1
       have r₂ := eq12 (M.op (M.op X0 X0) X1) x
       grind)
    | exact resolve eq25703 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25703
  have eq26010 : ∀ X0 X1 : G, (M.op x X0) = (k (M.op X0 X1) x) ∨ (M.op X0 X1) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq25751 X0 X1
       have i₂ := eq13504 X0 X1
       grind)
    | exact superpose eq13504 eq25751
    | (have j0 := eq25751 X0 X1
       grind)
    | exact resolve eq25751 eq13504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13504 eq25751
  have eq26127 : ∀ X0 X1 : G, x = (k (M.op (M.op X0 X0) X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq25966 X0 X1
       have i₂ := eq14140 (M.op X0 X0) X1
       grind)
    | exact superpose eq14140 eq25966
    | exact resolve eq25966 eq14140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25966
  have eq74490 : ∀ X0 : G, (M.op x X0) = (k (k X0 x) x) ∨ (k X0 x) = (M.op x X0) ∨ (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq26010 X0 X0
       have i₂ := eq13598 X0
       grind)
    | exact superpose eq13598 eq26010
    | (have j1 := eq13598 X0
       grind)
    | exact resolve eq26010 eq13598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13598 eq26010
  have eq74833 : ∀ X0 : G, (M.op x X0) = (k (k X0 x) x) ∨ (k X0 x) = (M.op x X0) := by
    intro X0
    first
    | (have j0 := eq74490 X0
       have j1 := eq12 X0 x
       grind)
    | (have r₁ := eq74490 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq74490 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74490
  have eq340940 : ∀ X0 : G, (τ (M.op x (σ X0))) = (k x (k (τ (M.op x (σ X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq15902 (σ X0) (M.op x (σ X0))
       have i₂ := eq21261 X0
       grind)
    | exact superpose eq21261 eq15902
    | exact resolve eq15902 eq21261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15902 eq21261
  have eq356137 : ∀ X0 : G, (τ (M.op x (σ X0))) = (k x (M.op X0 (τ (M.op x (σ X0))))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq340940 X0
       have i₂ := eq642 (τ (M.op x (σ X0))) X0
       grind)
    | exact superpose eq642 eq340940
    | (have j1 := eq642 X0 X0
       grind)
    | exact resolve eq340940 eq642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642 eq340940
  have eq356215 : ∀ X0 : G, (M.op x X0) = (τ (M.op x (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq356137 X0
       have i₂ := eq14377 X0 (τ (M.op x (σ X0)))
       grind)
    | exact superpose eq14377 eq356137
    | (have j0 := eq356137 X0
       grind)
    | exact resolve eq356137 eq14377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14377 eq356137
  have eq356767 : ∀ X0 : G, (M.op x (σ X0)) = (σ (M.op x X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (M.op x (σ X0))
       have i₂ := eq356215 X0
       grind)
    | exact superpose eq356215 eq11
    | (have j1 := eq356215 X0
       grind)
    | exact resolve eq11 eq356215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356215
  have eq357043 : (M.op x (σ y)) ≠ (M.op x (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq15551
       have i₂ := eq356767 y
       grind)
    | exact superpose eq356767 eq15551
    | (have j1 := eq356767 y
       grind)
    | (have r₁ := eq15551
       have r₂ := eq356767 y
       grind)
    | exact resolve eq15551 eq356767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356767
  have eq357227 : y = (M.op y y) := by grind
  clear eq357043
  have eq357531 : ∀ X0 : G, x = (k (M.op y X0) x) := by
    intro X0
    first
    | (have i₁ := eq26127 y X0
       have i₂ := eq357227
       grind)
    | exact superpose eq357227 eq26127
    | exact resolve eq26127 eq357227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26127
  have eq357633 : x = (M.op x y) := by
    first
    | (have i₁ := eq14140 y y
       have i₂ := eq357227
       grind)
    | exact superpose eq357227 eq14140
    | exact resolve eq14140 eq357227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14140
  have eq357883 : (σ x) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq15551
       have i₂ := eq357633
       grind)
    | exact superpose eq357633 eq15551
    | exact resolve eq15551 eq357633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15551 eq357633
  have eq358744 : x ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq357883
       have i₂ := eq15355
       grind)
    | exact superpose eq15355 eq357883
    | exact resolve eq357883 eq15355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357883
  have eq359156 : x = (k y x) := by
    first
    | (have i₁ := eq357531 y
       have i₂ := eq357227
       grind)
    | exact superpose eq357227 eq357531
    | exact resolve eq357531 eq357227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357227 eq357531
  have eq359256 : (σ x) = (k (σ y) x) := by
    first
    | (have i₁ := eq15560 y
       have i₂ := eq359156
       grind)
    | exact superpose eq359156 eq15560
    | exact resolve eq15560 eq359156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15560 eq359156
  have eq359338 : x = (k (σ y) x) := by
    first
    | (have i₁ := eq359256
       have i₂ := eq15355
       grind)
    | exact superpose eq15355 eq359256
    | exact resolve eq359256 eq15355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15355 eq359256
  have eq359480 : (k x x) = (M.op x (σ y)) ∨ x = (M.op x (σ y)) := by
    first
    | (have i₁ := eq74833 (σ y)
       have i₂ := eq359338
       grind)
    | exact superpose eq359338 eq74833
    | exact resolve eq74833 eq359338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74833 eq359338
  have eq359528 : (k x x) = (M.op x (σ y)) := by
    first
    | (have r₁ := eq359480
       have r₂ := eq358744
       grind)
    | exact resolve eq359480 eq358744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359480
  have eq359547 : x = (M.op x (σ y)) := by
    first
    | (have i₁ := eq359528
       have i₂ := eq13597
       grind)
    | exact superpose eq13597 eq359528
    | exact resolve eq359528 eq13597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13597 eq359528
  have eq359559 : False := by grind
  exact eq359559

/-- `Equation575`: `x = y ◇ (z ◇ (z ◇ (y ◇ x)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pxy_pyx_pxy_Equation575 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law575 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law575.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 (M.op X1 X0)))) = X0 := by
    intro X0 X1 X2
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op X3 (M.op X3 (M.op X1 X0))) = (M.op X1 (M.op X2 (M.op X2 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X3 (M.op X3 (M.op X1 X0))) X1 X2
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq41 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq41 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq55 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq55
    | (have j0 := eq55 (σ X0) (σ X1)
       grind)
    | exact resolve eq55 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq42 (τ X0)
       grind)
    | exact superpose eq42 eq18
    | exact resolve eq18 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq82 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq81 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq81
    | exact resolve eq81 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq90 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq82
    | exact resolve eq82 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq82
  have eq94 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq90 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq90
    | exact resolve eq90 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq117 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op X2 (M.op X2 X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (M.op X2 X0) X2 x X1
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq23
    | exact resolve eq23 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq66 x y
       grind)
    | exact superpose eq66 eq16
    | (have j1 := eq66 x y
       grind)
    | exact resolve eq16 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq171 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (M.op X1 (M.op X1 (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq9
    | exact resolve eq9 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq363 : ∀ X0 X1 : G, (σ X1) = (M.op X0 (M.op X0 (M.op (σ X1) (σ (M.op X1 X1))))) := by
    intro X0 X1
    first
    | (have i₁ := eq171 X1 x
       have i₂ := eq23 (σ (M.op X1 X1)) (σ X1) x X0
       grind)
    | (have i₁ := eq171 X0 (σ X0)
       have i₂ := eq23 (σ (M.op X0 X0)) (σ X0) x (σ X0)
       grind)
    | exact superpose eq23 eq171
    | exact resolve eq171 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq171
  have eq456 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq155
       have i₂ := eq94 y
       grind)
    | exact superpose eq94 eq155
    | exact resolve eq155 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq490 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq456
       have i₂ := eq55 x y
       grind)
    | exact superpose eq55 eq456
    | (have j1 := eq55 x y
       grind)
    | exact resolve eq456 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq456
  have eq491 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op y y) = (M.op y x) := by grind
  clear eq490
  have eq4301 : ∀ X0 : G, (σ x) = (M.op X0 (M.op X0 (M.op (σ y) (σ (M.op y y))))) ∨ (M.op y y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq117 (σ x) X0 (σ y)
       have i₂ := eq491
       grind)
    | exact superpose eq491 eq117
    | exact resolve eq117 eq491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq4309 : (σ x) = (σ y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq4301 x
       have i₂ := eq363 x y
       grind)
    | exact superpose eq363 eq4301
    | exact resolve eq4301 eq363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq363 eq4301
  have eq4315 : y = (τ (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq4309
       grind)
    | exact superpose eq4309 eq10
    | exact resolve eq10 eq4309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4309
  have eq4357 : x = y ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq4315
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq4315
    | exact resolve eq4315 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4315
  have eq4455 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4357
       grind)
    | exact superpose eq4357 eq16
    | exact resolve eq16 eq4357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4357
  have eq4456 : (M.op y y) = (M.op y x) := by
    first
    | (have r₁ := eq4455
       have r₂ := eq94 x
       grind)
    | exact resolve eq4455 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4455
  have eq4535 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op y (M.op y x)))) := by
    intro X0
    first
    | (have i₁ := eq117 y X0 y
       have i₂ := eq4456
       grind)
    | exact superpose eq4456 eq117
    | exact resolve eq117 eq4456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4456
  have eq4547 : x = y := by
    first
    | (have i₁ := eq4535 x
       have i₂ := eq117 x x y
       grind)
    | exact superpose eq117 eq4535
    | exact resolve eq4535 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq4535
  have eq4567 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4547
       grind)
    | exact superpose eq4547 eq16
    | exact resolve eq16 eq4547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4547
  have eq4569 : False := by grind
  exact eq4569

/-- `Equation58`: `x = x ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pyx_pxy_Equation58 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law58 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law58.models_iff G M).mp hM
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
  have eq21 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq24 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq23
  have eq53 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq136 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq53 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq13
    | (have j0 := eq13 (k (σ X0) (σ X1)) (M.op (σ X0) (σ X1))
       have j1 := eq53 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq53 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq13 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq143 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq136 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq144 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq143 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq150 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq144 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq144
    | (have j0 := eq144 X0 X1
       grind)
    | exact resolve eq144 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq151 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq150 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq487 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq151 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq151
    | exact resolve eq151 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq495 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq151 x y
       grind)
    | exact superpose eq151 eq16
    | (have j1 := eq151 x y
       grind)
    | exact resolve eq16 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151
  have eq516 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq487 X0 X1
       have i₂ := eq21 X0 X1
       grind)
    | exact superpose eq21 eq487
    | (have j0 := eq487 X0 X1
       grind)
    | exact resolve eq487 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq487
  have eq561 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq516 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq516
    | exact resolve eq516 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq656 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq495
       have i₂ := eq561 x y
       grind)
    | exact superpose eq561 eq495
    | (have j1 := eq561 (σ x) (σ y)
       grind)
    | (have r₁ := eq495
       have r₂ := eq561 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq495
       have r₂ := eq561 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq495 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495 eq561
  have eq659 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq656
  have eq709 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq659
       grind)
    | exact superpose eq659 eq10
    | exact resolve eq10 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq747 : x = y ∨ x = y := by
    first
    | (have i₁ := eq709
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq709
    | exact resolve eq709 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq748 : x = y := by grind
  clear eq747
  have eq750 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq748
       grind)
    | exact superpose eq748 eq16
    | exact resolve eq16 eq748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748
  have eq751 : False := by grind
  exact eq751
