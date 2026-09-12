import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq90 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq303 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq328 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq303 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303
  have eq329 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq328 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq336 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq329 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq329 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq329 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq347 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq336 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq336
    | (have j0 := eq336 X0 X1
       grind)
    | exact resolve eq336 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq348 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq347 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq353 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq348 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq348
    | exact resolve eq348 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq348 x y
       grind)
    | exact superpose eq348 eq16
    | exact resolve eq16 eq348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq543 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq353 X0 (τ X1)
       grind)
    | exact superpose eq353 eq17
    | exact resolve eq17 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq353
  have eq563 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq543 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq543
    | exact resolve eq543 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq572 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq563 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq563
    | exact resolve eq563 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq594 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq365
       have i₂ := eq572 x y
       grind)
    | exact superpose eq572 eq365
    | exact resolve eq365 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365 eq572
  have eq595 : False := by grind
  exact eq595

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq78 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq99
    | exact resolve eq99 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq136 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq11 sF1 (σ X0)
       grind)
    | exact superpose eq11 eq37
    | (have j1 := eq11 (σ (M.op x y)) (σ X0)
       grind)
    | exact resolve eq37 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq159 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq136 eq16
    | exact resolve eq16 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq50 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 y
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq222 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq523 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq52 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq533 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq523 X0
       grind)
    | exact superpose eq523 eq14
    | exact resolve eq14 eq523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq523
  have eq820 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq533 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq533
    | exact resolve eq533 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq822 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq53 eq533
    | exact resolve eq533 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq824 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq54 eq533
    | exact resolve eq533 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq533
  have eq885 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq886 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq77 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq887 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq885 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885
  have eq912 : x ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq822 eq13
    | (have j0 := eq13 y x
       grind)
    | exact resolve eq13 eq822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3915 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq887 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq887
    | (have j0 := eq887 (τ X0)
       grind)
    | exact resolve eq887 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq887
  have eq3923 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3915 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3915
    | (have j0 := eq3915 X0
       grind)
    | exact resolve eq3915 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3915
  have eq3929 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3923 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3923
    | (have j0 := eq3923 X0
       grind)
    | exact resolve eq3923 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3923
  have eq6386 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq78 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq78
    | (have j0 := eq78 x
       grind)
    | exact resolve eq78 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq6413 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq6386
  have eq6418 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq6413
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq6413
    | exact resolve eq6413 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq6413
  have eq6436 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq6418
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq6418 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6418
  have eq6440 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq6436 eq49
    | exact resolve eq49 eq6436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq6436
  have eq6882 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq137
    | (have j0 := eq137 (M.op x y)
       grind)
    | exact resolve eq137 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq6907 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq6882
  have eq6910 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq136 eq6907
    | exact resolve eq6907 eq136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq6907
  have eq6942 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have j1 := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq6910
       have r₂ := eq13 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq6910 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6910
  have eq6978 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq6942 eq159
    | exact resolve eq159 eq6942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq159 eq6942
  have eq9437 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq101 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq9438 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq9437
    | exact resolve eq9437 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9437
  have eq9449 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq9438
       have r₂ := eq27
       grind)
    | exact resolve eq9438 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9438
  have eq9451 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq9449
    | exact resolve eq9449 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9449
  have eq9455 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | exact superpose eq9451 eq14
    | exact resolve eq14 eq9451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9476 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq9451 eq820
    | exact resolve eq820 eq9451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9489 : ∀ X0 : G, (σ x) = (M.op (M.op (σ y) X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq9455 x
       have i₂ := eq820 sF3 x
       grind)
    | exact superpose eq820 eq9455
    | exact resolve eq9455 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9455
  have eq10269 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq9476 eq9489
    | exact resolve eq9489 eq9476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9476
  have eq10319 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq10269
  have eq10555 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq10319 eq9451
    | exact resolve eq9451 eq10319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9451
  have eq10556 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq10319 eq9489
    | exact resolve eq9489 eq10319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9489 eq10319
  have eq10589 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq10556
  have eq10590 : y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq10555
  have eq10597 : ∀ X0 : G, x = (M.op (M.op y (M.op y X0)) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq10590
       grind)
    | exact superpose eq10590 eq14
    | exact resolve eq14 eq10590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10643 : ∀ X0 : G, x = (M.op (M.op y X0) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq10597 X0
       have i₂ := eq820 y X0
       grind)
    | exact superpose eq820 eq10597
    | exact resolve eq10597 eq820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq820 eq10597
  have eq11660 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10643 x
       have i₂ := eq10590
       grind)
    | exact superpose eq10590 eq10643
    | exact resolve eq10643 eq10590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10643
  have eq11720 : x = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq11660
  have eq12396 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10590
       have i₂ := eq11720
       grind)
    | exact superpose eq11720 eq10590
    | exact resolve eq10590 eq11720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10590 eq11720
  have eq12437 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq12396
  have eq12447 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12437 eq222
    | exact resolve eq222 eq12437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222
  have eq12470 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12437 eq824
    | exact resolve eq824 eq12437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq16319 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12470 eq12447
    | exact resolve eq12447 eq12470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12447 eq12470
  have eq16362 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq16319
  have eq16368 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq16362
    | exact resolve eq16362 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16362
  have eq16410 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq16368 eq12437
    | exact resolve eq12437 eq16368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12437 eq16368
  have eq16423 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq16410
  have eq16688 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq16423 eq29
    | exact resolve eq29 eq16423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq16423
  have eq16848 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq16688
    | exact resolve eq16688 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16688
  have eq16849 : x = (M.op x y) ∨ x = y := by grind
  clear eq16848
  have eq16850 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq16849 eq20
    | exact resolve eq20 eq16849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16934 : x = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq16849 eq822
    | exact resolve eq822 eq16849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq822
  have eq17006 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq16850
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16850
    | exact resolve eq16850 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16850
  have eq17509 : x ≠ x ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq16934
       grind)
    | exact superpose eq16934 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq16934
       grind)
    | exact resolve eq13 eq16934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16934
  have eq17550 : x = (k x x) ∨ x = y := by grind
  clear eq17509
  have eq17748 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq886 x x
       have i₂ := eq17550
       grind)
    | exact superpose eq17550 eq886
    | (have j0 := eq886 x x
       grind)
    | exact resolve eq886 eq17550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886 eq17550
  have eq17751 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq17748
  have eq17752 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by grind
  clear eq17751
  have eq17761 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq17752
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17752
    | exact resolve eq17752 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17752
  have eq17833 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq17006 eq17761
    | exact resolve eq17761 eq17006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17006 eq17761
  have eq17911 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq17833
  have eq20067 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq17911 eq6978
    | exact resolve eq6978 eq17911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6978 eq17911
  have eq20146 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq30 eq20067
    | exact resolve eq20067 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq20067
  have eq21154 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq20146 eq11
    | (have j0 := eq11 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq11 eq20146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20146
  have eq21172 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq21154
  have eq22440 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq21172 eq213
    | exact resolve eq213 eq21172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq21172
  have eq23684 : y = (M.op x y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq16849 eq22440
    | exact resolve eq22440 eq16849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22440
  have eq23730 : y = (M.op x y) ∨ x = y := by grind
  clear eq23684
  have eq23732 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq23730
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23730
    | exact resolve eq23730 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23730
  have eq23825 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq23732 eq16849
    | exact resolve eq16849 eq23732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16849 eq23732
  have eq23836 : x = y := by grind
  clear eq23825
  have eq24326 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq23836
       grind)
    | exact superpose eq23836 eq18
    | exact resolve eq18 eq23836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq24327 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq23836
       grind)
    | exact superpose eq23836 eq24
    | exact resolve eq24 eq23836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq24468 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24327
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24327
    | exact resolve eq24327 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24327
  have eq24504 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq24468 eq26
    | exact resolve eq26 eq24468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq24468
  have eq25714 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq24504 eq6440
    | exact resolve eq6440 eq24504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6440
  have eq25722 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq24504 eq10589
    | exact resolve eq10589 eq24504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10589 eq24504
  have eq25799 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq25722
  have eq25813 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25799
       have i₂ := eq23836
       grind)
    | exact superpose eq23836 eq25799
    | exact resolve eq25799 eq23836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23836 eq25799
  have eq25821 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25813
       have i₂ := eq24326
       grind)
    | exact superpose eq24326 eq25813
    | exact resolve eq25813 eq24326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25813
  have eq25822 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq25821
  have eq28590 : x ≠ (τ (M.op (σ x) (σ y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3929 x
       have i₂ := eq25714
       grind)
    | exact superpose eq25714 eq3929
    | (have j0 := eq3929 x
       grind)
    | exact resolve eq3929 eq25714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3929
  have eq28622 : x ≠ (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq28590
       have i₂ := eq24326
       grind)
    | exact superpose eq24326 eq28590
    | exact resolve eq28590 eq24326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28590
  have eq30428 : x ≠ (τ (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq25822 eq28622
    | exact resolve eq28622 eq25822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25822 eq28622
  have eq30435 : x ≠ (τ (σ x)) ∨ x = (M.op x y) := by grind
  clear eq30428
  have eq30436 : x = (M.op x y) := by
    first
    | (have r₁ := eq30435
       have r₂ := eq28
       grind)
    | exact resolve eq30435 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq30435
  have eq30438 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq30436 eq20
    | exact resolve eq20 eq30436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq30523 : x ≠ x ∨ (k x x) = (M.op x x) := by
    first
    | exact superpose eq30436 eq912
    | (have r₁ := eq912
       have r₂ := eq30436
       grind)
    | exact resolve eq912 eq30436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq30536 : (k x x) = (M.op x x) := by grind
  clear eq30523
  have eq30544 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq30536
       have i₂ := eq24326
       grind)
    | exact superpose eq24326 eq30536
    | exact resolve eq30536 eq24326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24326 eq30536
  have eq30618 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq30438
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq30438
    | exact resolve eq30438 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30438
  have eq30621 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq30544
       have i₂ := eq25714
       grind)
    | exact superpose eq25714 eq30544
    | exact resolve eq30544 eq25714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25714 eq30544
  have eq30681 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq30436 eq30621
    | exact resolve eq30621 eq30436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30436 eq30621
  have eq31082 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30681 eq15
    | exact resolve eq15 eq30681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30681
  have eq31134 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq31082
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq31082
    | exact resolve eq31082 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq31082
  have eq31150 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30618 eq31134
    | exact resolve eq31134 eq30618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30618 eq31134
  have eq31164 : False := by grind
  exact eq31164

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,X) = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyy_pxy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq177 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq180 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : (σ (M.op x x)) = (k (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq39 (M.op x x)
       have i₂ := eq180 x
       grind)
    | exact superpose eq180 eq39
    | exact resolve eq39 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : (τ (M.op (σ x) (σ x))) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | (have i₁ := eq141 (M.op sF2 sF2)
       have i₂ := eq180 sF2
       grind)
    | exact superpose eq180 eq141
    | exact resolve eq141 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141
  have eq635 : (M.op x y) = (k y x) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
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
  have eq647 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
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
  have eq658 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq658 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq683 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq816 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq177 eq192
    | exact resolve eq192 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq192
  have eq824 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq816 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq816
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq816 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq833 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq816 X0
       grind)
    | exact superpose eq816 eq16
    | exact resolve eq16 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq835 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq824 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq866 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq833 X0 (M.op X0 X1)
       have i₂ := eq16 X0 X0 X1
       grind)
    | exact superpose eq16 eq833
    | exact resolve eq833 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq1964 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq635
       grind)
    | exact superpose eq635 eq39
    | exact resolve eq39 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq1965 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1964
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1964
    | exact resolve eq1964 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1964
  have eq1967 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq20 eq1965
    | exact resolve eq1965 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1965
  have eq17172 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1967 eq647
    | exact resolve eq647 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17181 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17172
       have r₂ := eq27
       grind)
    | exact resolve eq17172 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17172
  have eq17188 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17181 eq230
    | exact resolve eq230 eq17181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq17213 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17181 eq866
    | exact resolve eq866 eq17181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17219 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17181 eq180
    | exact resolve eq180 eq17181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17181
  have eq17228 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq1967 eq17219
    | exact resolve eq17219 eq1967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1967 eq17219
  have eq17232 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq17213
    | exact resolve eq17213 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17213
  have eq17235 : y = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq31 eq17188
    | exact resolve eq17188 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17188
  have eq17238 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq635 eq17235
    | exact resolve eq17235 eq635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635 eq17235
  have eq17245 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17228 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq17228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17264 : ∀ X0 : G, (σ x) ≠ X0 ∨ (σ x) = (k X0 (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    intro X0
    first
    | exact superpose eq17228 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq17228
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq17228
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq17228
       grind)
    | exact resolve eq13 eq17228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17228
  have eq17270 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq17245
  have eq17276 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq17264 (σ y)
       grind)
    | (have r₁ := eq17270
       have r₂ := eq17264 (k (σ y) (σ y))
       grind)
    | (have r₁ := eq17270
       have r₂ := eq17264 (σ y)
       grind)
    | exact resolve eq17270 eq17264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17264 eq17270
  have eq17900 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17238 eq816
    | exact resolve eq816 eq17238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17238
  have eq17905 : y = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq17900
    | exact resolve eq17900 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17900
  have eq17943 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq866 x x
       have i₂ := eq17905
       grind)
    | exact superpose eq17905 eq866
    | exact resolve eq866 eq17905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17905
  have eq17961 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17943
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17943
    | exact resolve eq17943 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17943
  have eq17962 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq17961
  have eq17996 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq816 y
       have i₂ := eq17962
       grind)
    | exact superpose eq17962 eq816
    | exact resolve eq816 eq17962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17962
  have eq18001 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq17996
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17996
    | exact resolve eq17996 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17996
  have eq18002 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq18001
  have eq18011 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18002 eq27
    | exact resolve eq27 eq18002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18708 : (τ (σ x)) = (k y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17276 eq115
    | exact resolve eq115 eq17276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq17276
  have eq18725 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ x = (k y y) := by
    first
    | exact superpose eq29 eq18708
    | exact resolve eq18708 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18708
  have eq18849 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17232 eq816
    | exact resolve eq816 eq17232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17232
  have eq18856 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq26 eq18849
    | exact resolve eq18849 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18849
  have eq18857 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by grind
  clear eq18856
  have eq18889 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq18002 eq18857
    | exact resolve eq18857 eq18002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18857
  have eq18918 : (M.op x y) = (M.op x x) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18002 eq18889
    | exact resolve eq18889 eq18002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18002 eq18889
  have eq18931 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq197
       have i₂ := eq18918
       grind)
    | exact superpose eq18918 eq197
    | exact resolve eq197 eq18918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197 eq18918
  have eq18985 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq18931
    | exact resolve eq18931 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18931
  have eq20230 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq866 x x
       have i₂ := eq18725
       grind)
    | exact superpose eq18725 eq866
    | exact resolve eq866 eq18725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18725
  have eq20248 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ x = (M.op y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq20230
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20230
    | exact resolve eq20230 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20230
  have eq20254 : x = (k y y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq20248
       have r₂ := eq18011
       grind)
    | exact resolve eq20248 eq18011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18011 eq20248
  have eq20266 : y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq835 y
       have i₂ := eq20254
       grind)
    | exact superpose eq20254 eq835
    | (have j0 := eq835 y
       grind)
    | exact resolve eq835 eq20254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20272 : y = (M.op x y) ∨ y = (M.op y y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20266
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20266
    | exact resolve eq20266 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20266
  have eq20273 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq20272
  have eq20317 : (k y y) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq683 y
       have i₂ := eq20273
       grind)
    | exact superpose eq20273 eq683
    | exact resolve eq683 eq20273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20273
  have eq20329 : (k y y) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq20317
       have r₂ := eq13 (k y y) y
       grind)
    | (have r₁ := eq20317
       have r₂ := eq13 y y
       grind)
    | (have r₁ := eq20317
       have r₂ := eq13 x y
       grind)
    | exact resolve eq20317 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20317
  have eq20340 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20254 eq20329
    | exact resolve eq20329 eq20254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20254 eq20329
  have eq20341 : x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq20340
  have eq20377 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq816 y
       have i₂ := eq20341
       grind)
    | exact superpose eq20341 eq816
    | exact resolve eq816 eq20341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20341
  have eq20385 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq20377
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq20377
    | exact resolve eq20377 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq20377
  have eq20386 : y = (M.op x y) := by grind
  clear eq20385
  have eq20396 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq20386
       grind)
    | exact superpose eq20386 eq24
    | exact resolve eq24 eq20386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq20398 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq20386
       grind)
    | exact superpose eq20386 eq40
    | exact resolve eq40 eq20386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq20448 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20396 eq20
    | exact resolve eq20 eq20396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20396
  have eq20714 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20448 eq18985
    | exact resolve eq18985 eq20448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18985
  have eq27490 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20714 eq647
    | exact resolve eq647 eq20714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20714
  have eq27499 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq27490
  have eq105269 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27499 eq866
    | exact resolve eq866 eq27499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866 eq27499
  have eq105316 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq105269
    | exact resolve eq105269 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105269
  have eq105317 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq105316
  have eq105375 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq105317 eq816
    | exact resolve eq816 eq105317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816 eq105317
  have eq105382 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq26 eq105375
    | exact resolve eq105375 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105375
  have eq105383 : x = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq105382
  have eq105411 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq105383 eq11
    | exact resolve eq11 eq105383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105449 : ∀ X0 : G, x ≠ X0 ∨ x = (k X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq105383 eq13
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq105383
       grind)
    | exact resolve eq13 eq105383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105383
  have eq105456 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq105411
  have eq105473 : x = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq105449 (M.op x y)
       grind)
    | (have r₁ := eq105456
       have r₂ := eq105449 (k (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq105456
       have r₂ := eq105449 (M.op x y)
       grind)
    | exact resolve eq105456 eq105449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105449 eq105456
  have eq105560 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq105473 eq20398
    | exact resolve eq20398 eq105473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20398 eq105473
  have eq105574 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq105560
    | exact resolve eq105560 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105560
  have eq105596 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20448 eq105574
    | exact resolve eq105574 eq20448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105574
  have eq105607 : (σ x) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq105596
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq105596
    | exact resolve eq105596 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105596
  have eq105709 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq105607 eq835
    | (have j0 := eq835 (σ y)
       grind)
    | exact resolve eq835 eq105607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq835
  have eq105715 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq105709
    | exact resolve eq105709 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105709
  have eq105716 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq105715
  have eq105813 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq105716 eq180
    | exact resolve eq180 eq105716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq105814 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq105716 eq683
    | exact resolve eq683 eq105716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683 eq105716
  have eq105825 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq105814
       have r₂ := eq13 (k (σ y) (σ y)) (σ y)
       grind)
    | (have r₁ := eq105814
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq105814 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105814
  have eq105826 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq105607 eq105813
    | exact resolve eq105813 eq105607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105813
  have eq105847 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq105607 eq105825
    | exact resolve eq105825 eq105607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105607 eq105825
  have eq105860 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq105826 eq105847
    | exact resolve eq105847 eq105826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105847
  have eq105870 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq105826 eq27
    | exact resolve eq27 eq105826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105826
  have eq105901 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq105870
       have r₂ := eq20448
       grind)
    | exact resolve eq105870 eq20448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20448 eq105870
  have eq105902 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq105901 eq26
    | exact resolve eq26 eq105901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq105903 : y = (τ (σ x)) := by
    first
    | exact superpose eq105901 eq31
    | exact resolve eq31 eq105901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq105960 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq105901 eq647
    | exact resolve eq647 eq105901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq106106 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq105960
  have eq106162 : (σ y) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq105860 eq106106
    | exact resolve eq106106 eq105860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105860 eq106106
  have eq106210 : x = y := by
    first
    | exact superpose eq29 eq105903
    | exact resolve eq105903 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq105903
  have eq106215 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq105901 eq106162
    | exact resolve eq106162 eq105901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105901 eq106162
  have eq106251 : x = (M.op x y) := by
    first
    | (have i₁ := eq106210
       have i₂ := eq20386
       grind)
    | exact superpose eq20386 eq106210
    | exact resolve eq106210 eq20386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20386 eq106210
  have eq106253 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq659 (σ x)
       grind)
    | (have r₁ := eq106215
       have r₂ := eq659 (σ x)
       grind)
    | exact resolve eq106215 eq659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659 eq106215
  have eq106300 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq106251
       grind)
    | exact superpose eq106251 eq22
    | exact resolve eq22 eq106251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq106251
  have eq107122 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq106300 eq20
    | exact resolve eq20 eq106300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq106300
  have eq109499 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq106253 eq105902
    | exact resolve eq105902 eq106253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105902 eq106253
  have eq109619 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq109499 eq27
    | exact resolve eq27 eq109499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq109499
  have eq109668 : False := by grind
  exact eq109668

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pyy_x_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq174 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
    intro X0
    first
    | (have i₁ := eq16 y x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y x X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) (σ x) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq178 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq174
    | (have j0 := eq174 y
       grind)
    | exact resolve eq174 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq183 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op x y) (M.op x y)) X0) y) X0) = X0 := by
    intro X0
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq26 eq175
    | (have j0 := eq175 (σ y)
       grind)
    | exact resolve eq175 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq188 : ∀ X0 : G, (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq185 eq16
    | exact resolve eq16 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op x X0) (M.op x y)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : y = (M.op (M.op y y) y) := by
    first
    | exact superpose eq180 eq183
    | exact resolve eq183 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq550 : ∀ X0 : G, (M.op (M.op (M.op (M.op y y) X0) y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op y y) y
       have i₂ := eq547
       grind)
    | exact superpose eq547 eq16
    | exact resolve eq16 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq555 : (σ y) = (M.op (M.op (σ y) (σ y)) (σ y)) := by
    first
    | exact superpose eq185 eq188
    | exact resolve eq188 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq558 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ y) (σ y)) X0) (σ y)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq555 eq16
    | exact resolve eq16 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq564 : ∀ X0 : G, (M.op y X0) = (M.op y (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq550 (M.op y X0)
       have i₂ := eq16 y y X0
       grind)
    | exact superpose eq16 eq550
    | exact resolve eq550 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq574 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq558 (M.op sF3 x)
       have i₂ := eq16 sF3 sF3 x
       grind)
    | exact superpose eq16 eq558
    | exact resolve eq558 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq616 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq618 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq680 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq681 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq681 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq788 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq616
       grind)
    | exact superpose eq616 eq40
    | exact resolve eq40 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq789 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq788
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq788
    | exact resolve eq788 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq788
  have eq791 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq789
    | exact resolve eq789 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq849 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | exact superpose eq177 eq191
    | exact resolve eq191 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq871 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 X0) X0
       have i₂ := eq849 X0
       grind)
    | exact superpose eq849 eq16
    | exact resolve eq16 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq872 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 (M.op X0 X0) X1
       have i₂ := eq849 X0
       grind)
    | exact superpose eq849 eq16
    | exact resolve eq16 eq849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq849
  have eq917 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq177 eq871
    | exact resolve eq871 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq921 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq178 eq871
    | exact resolve eq871 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1626 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq791 eq618
    | exact resolve eq618 eq791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618 eq791
  have eq1633 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1626
       have r₂ := eq27
       grind)
    | exact resolve eq1626 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626
  have eq1653 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1633 eq13
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1633
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1633
       grind)
    | exact resolve eq13 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1633
  have eq1654 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq1653 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653
  have eq1683 : (τ (σ y)) = (k y (τ (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1654 eq107
    | exact resolve eq107 eq1654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq1654
  have eq1692 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq1683
    | exact resolve eq1683 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1683
  have eq1704 : y = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq682 y
       grind)
    | (have r₁ := eq1692
       have r₂ := eq682 y
       grind)
    | exact resolve eq1692 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq1692
  have eq1721 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq872 y X0
       have i₂ := eq1704
       grind)
    | exact superpose eq1704 eq872
    | exact resolve eq872 eq1704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1722 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq871 y X0
       have i₂ := eq1704
       grind)
    | exact superpose eq1704 eq871
    | exact resolve eq871 eq1704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq1724 : ∀ X0 : G, y ≠ y ∨ y = (k X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1704
       grind)
    | exact superpose eq1704 eq13
    | (have r₁ := eq13 X0 y
       have r₂ := eq1704
       grind)
    | exact resolve eq13 eq1704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1704
  have eq1725 : ∀ X0 : G, y = (k X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1724 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1724
  have eq1727 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1721 X0
       have i₂ := eq564 X0
       grind)
    | exact superpose eq564 eq1721
    | exact resolve eq1721 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564 eq1721
  have eq1744 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 y
       have i₂ := eq1725 y
       grind)
    | exact superpose eq1725 eq36
    | exact resolve eq36 eq1725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1755 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1744
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1744
    | exact resolve eq1744 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744
  have eq1921 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1755 eq680
    | (have j0 := eq680 (σ y) (σ y)
       grind)
    | (have r₁ := eq680 (σ y) (σ y)
       have r₂ := eq1755
       grind)
    | exact resolve eq680 eq1755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755
  have eq1922 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1921
  have eq1923 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1922
  have eq2117 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1923 eq872
    | exact resolve eq872 eq1923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq1923
  have eq2123 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq574 eq2117
    | exact resolve eq2117 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq2117
  have eq2359 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1722 X0
       have i₂ := eq1727 X0
       grind)
    | exact superpose eq1727 eq1722
    | exact resolve eq1722 eq1727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1722
  have eq2388 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2359 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2359
  have eq2449 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1727 X0
       have i₂ := eq2388 X0
       grind)
    | exact superpose eq2388 eq1727
    | exact resolve eq1727 eq2388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1727
  have eq2464 : ∀ X0 X1 : G, (M.op (M.op (M.op y X1) X0) X1) = X1 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 y X0
       have i₂ := eq2388 X0
       grind)
    | exact superpose eq2388 eq16
    | exact resolve eq16 eq2388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2483 : ∀ X0 : G, y = (M.op X0 y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2449 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2449
  have eq2491 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq2388 eq2464
    | exact resolve eq2464 eq2388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2388 eq2464
  have eq2571 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq2483 x
       grind)
    | exact superpose eq2483 eq18
    | (have j1 := eq2483 x
       grind)
    | exact resolve eq18 eq2483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2483
  have eq2614 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2571 eq185
    | exact resolve eq185 eq2571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2629 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2571 eq921
    | exact resolve eq921 eq2571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2640 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2629 eq2614
    | exact resolve eq2614 eq2629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2614 eq2629
  have eq2644 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2640
    | exact resolve eq2640 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2640
  have eq2645 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2571 eq2644
    | exact resolve eq2644 eq2571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2644
  have eq2647 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2645 eq31
    | exact resolve eq31 eq2645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq2645
  have eq2726 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq2647
    | exact resolve eq2647 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2647
  have eq2732 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq24
       have i₂ := eq2726
       grind)
    | exact superpose eq2726 eq24
    | exact resolve eq24 eq2726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2760 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1725 X0
       have i₂ := eq2726
       grind)
    | exact superpose eq2726 eq1725
    | exact resolve eq1725 eq2726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725 eq2726
  have eq2782 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq2760 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2760
  have eq2805 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2571 eq2782
    | (have j0 := eq2782 X0
       grind)
    | exact resolve eq2782 eq2571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2782
  have eq2806 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2805 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2805
  have eq2814 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq2732
    | exact resolve eq2732 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2732
  have eq3456 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2806 eq37
    | exact resolve eq37 eq2806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2806
  have eq3462 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq3456
    | exact resolve eq3456 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3456
  have eq3527 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3462 eq680
    | (have j0 := eq680 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq680 (σ (M.op x y)) (σ (M.op x y))
       have r₂ := eq3462
       grind)
    | exact resolve eq680 eq3462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3462
  have eq3528 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3527
  have eq3529 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3528
  have eq3644 : ∀ X0 : G, (M.op (M.op (M.op (σ (M.op x y)) X0) (σ (M.op x y))) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq3529 eq16
    | exact resolve eq16 eq3529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3529
  have eq3661 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2491 eq3644
    | exact resolve eq3644 eq2491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2491 eq3644
  have eq3682 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2814 eq3661
    | exact resolve eq3661 eq2814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3661
  have eq3710 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq3682 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3682
  have eq3716 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2571 eq3710
    | (have j0 := eq3710 X0
       grind)
    | exact resolve eq3710 eq2571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3710
  have eq3717 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3716 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3716
  have eq3724 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq3717 eq2123
    | exact resolve eq2123 eq3717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2123 eq3717
  have eq3762 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq3724 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3724
  have eq3961 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3762 eq26
    | (have j1 := eq3762 (σ x)
       grind)
    | exact resolve eq26 eq3762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3762
  have eq3992 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3961 eq27
    | exact resolve eq27 eq3961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3961
  have eq4021 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2814 eq3992
    | (have r₁ := eq3992
       have r₂ := eq2814
       grind)
    | exact resolve eq3992 eq2814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3992
  have eq4022 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq4021
  have eq4023 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq4022
  have eq4024 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2571 eq4023
    | exact resolve eq4023 eq2571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2571 eq4023
  have eq4025 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4024
  have eq4027 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4025 eq27
    | exact resolve eq27 eq4025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4030 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4025 eq185
    | exact resolve eq185 eq4025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq4045 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4025 eq921
    | exact resolve eq921 eq4025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq4057 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4045 eq4030
    | exact resolve eq4030 eq4045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4030
  have eq4061 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq4057
    | exact resolve eq4057 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4057
  have eq4062 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4025 eq4061
    | exact resolve eq4061 eq4025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4025 eq4061
  have eq4063 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2814 eq4027
    | exact resolve eq4027 eq2814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2814 eq4027
  have eq4064 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4063
  have eq4065 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq4064
       have r₂ := eq4062
       grind)
    | exact resolve eq4064 eq4062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4062 eq4064
  have eq4160 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq4065
       grind)
    | exact superpose eq4065 eq18
    | exact resolve eq18 eq4065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4171 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq917
       have i₂ := eq4065
       grind)
    | exact superpose eq4065 eq917
    | exact resolve eq917 eq4065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq4233 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4045 eq13
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq4045
       grind)
    | exact resolve eq13 eq4045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4045
  have eq4246 : ∀ X0 : G, (σ x) = (k X0 (σ x)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq4233 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4233
  have eq4516 : (τ (σ x)) = (k x (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4246 eq90
    | exact resolve eq90 eq4246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq4246
  have eq4523 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq4516
    | exact resolve eq4516 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4516
  have eq4576 : y = (M.op (M.op x y) y) ∨ x = y := by
    first
    | exact superpose eq4171 eq180
    | exact resolve eq180 eq4171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq4171
  have eq4601 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4160 eq4576
    | exact resolve eq4576 eq4160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4160 eq4576
  have eq4647 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq4601
  have eq4648 : x = y := by
    first
    | (have r₁ := eq4647
       have r₂ := eq4065
       grind)
    | exact resolve eq4647 eq4065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4065 eq4647
  have eq4654 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4648
       grind)
    | exact superpose eq4648 eq18
    | exact resolve eq18 eq4648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4655 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4648
       grind)
    | exact superpose eq4648 eq24
    | exact resolve eq24 eq4648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq4668 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq616
       have i₂ := eq4648
       grind)
    | exact superpose eq4648 eq616
    | exact resolve eq616 eq4648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616 eq4648
  have eq4698 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq4523 eq4668
    | exact resolve eq4668 eq4523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4523 eq4668
  have eq4699 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq4698
  have eq4702 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4655
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4655
    | exact resolve eq4655 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4655
  have eq4703 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4699
       have i₂ := eq4654
       grind)
    | exact superpose eq4654 eq4699
    | exact resolve eq4699 eq4654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4699
  have eq4704 : x = (M.op x y) := by grind
  clear eq4703
  have eq4705 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4702 eq26
    | exact resolve eq26 eq4702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4702
  have eq4773 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq4704
       grind)
    | exact superpose eq4704 eq22
    | exact resolve eq22 eq4704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq4801 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4773 eq20
    | exact resolve eq20 eq4773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4773
  have eq4971 : ∀ X0 : G, x ≠ (M.op x y) ∨ (M.op x y) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq4654
       grind)
    | exact superpose eq4654 eq13
    | exact resolve eq13 eq4654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4654
  have eq4997 : ∀ X0 : G, (M.op x y) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq4971 X0
       grind)
    | (have r₁ := eq4971 X0
       have r₂ := eq4704
       grind)
    | exact resolve eq4971 eq4704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4971
  have eq5000 : ∀ X0 : G, (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq4997 X0
       have i₂ := eq4704
       grind)
    | exact superpose eq4704 eq4997
    | exact resolve eq4997 eq4704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4704 eq4997
  have eq5167 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq5000 eq37
    | exact resolve eq37 eq5000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq5000
  have eq5175 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq5167
    | exact resolve eq5167 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5167
  have eq5180 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq4801 eq5175
    | exact resolve eq5175 eq4801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5175
  have eq5196 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq5180 eq680
    | (have j0 := eq680 (σ x) (σ x)
       grind)
    | (have r₁ := eq680 (σ x) (σ x)
       have r₂ := eq5180
       grind)
    | exact resolve eq680 eq5180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq680 eq5180
  have eq5197 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5196
  have eq5198 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5197
  have eq5253 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5198 eq4705
    | exact resolve eq4705 eq5198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4705 eq5198
  have eq5297 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq5253 eq27
    | exact resolve eq27 eq5253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq5253
  have eq5329 : False := by grind
  exact eq5329

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,Y) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyy_x_pyx_y_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op X1 X0) (M.op X1 X2)) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X1 : G, (M.op (M.op X1 X1) X1) = X1 := by
    intro X1
    first
    | (have i₁ := eq30 X1 x x X1
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq30
    | exact resolve eq30 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq70 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq9
    | exact resolve eq9 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq81 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq70 X1 (M.op X1 X0)
       have i₂ := eq9 X1 X1 X0
       grind)
    | exact superpose eq9 eq70
    | exact resolve eq70 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq114 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq81
    | (have j0 := eq81 (σ X0) (σ X1)
       grind)
    | exact resolve eq81 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op X1 X2) = (k X2 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 X1
       have i₂ := eq81 X0 X1
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq81 (M.op X1 X1) X1
       grind)
    | exact superpose eq81 eq12
    | (have j0 := eq12 X2 X1
       have j1 := eq81 X2 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq81 X0 X0
       grind)
    | (have r₁ := eq12 X0 (M.op X1 X1)
       have r₂ := eq81 (M.op (M.op X1 X1) (M.op X1 X1)) X1
       grind)
    | exact resolve eq12 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq850 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq125 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq871 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq850 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq872 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq871 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq880 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq872 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq872
    | exact resolve eq872 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq887 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq880 X0
       have i₂ := eq872 X0
       grind)
    | exact superpose eq872 eq880
    | exact resolve eq880 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872 eq880
  have eq928 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq114 y x
       grind)
    | exact superpose eq114 eq16
    | (have j1 := eq114 y x
       grind)
    | exact resolve eq16 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq1019 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq84 (σ X0) (σ X0)
       have i₂ := eq887 X0
       grind)
    | exact superpose eq887 eq84
    | exact resolve eq84 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2586 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq928
       have i₂ := eq887 x
       grind)
    | exact superpose eq887 eq928
    | exact resolve eq928 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887 eq928
  have eq2587 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2586
       have i₂ := eq81 y x
       grind)
    | exact superpose eq81 eq2586
    | (have j1 := eq81 y x
       grind)
    | exact resolve eq2586 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq2586
  have eq2604 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq2587
  have eq2611 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2604
       grind)
    | exact superpose eq2604 eq10
    | exact resolve eq10 eq2604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2604
  have eq2654 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq2611
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq2611
    | exact resolve eq2611 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2611
  have eq2655 : y = (M.op x x) := by grind
  clear eq2654
  have eq2671 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1019 x
       have i₂ := eq2655
       grind)
    | exact superpose eq2655 eq1019
    | exact resolve eq1019 eq2655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019
  have eq2686 : y = (M.op x y) := by
    first
    | (have i₁ := eq84 x x
       have i₂ := eq2655
       grind)
    | exact superpose eq2655 eq84
    | exact resolve eq84 eq2655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq2655
  have eq2804 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2671
       grind)
    | exact superpose eq2671 eq16
    | exact resolve eq16 eq2671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2671
  have eq2826 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq2804
       have i₂ := eq2686
       grind)
    | exact superpose eq2686 eq2804
    | exact resolve eq2804 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2686 eq2804
  have eq2827 : False := by grind
  exact eq2827

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pxy_pxx_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq43 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
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
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op X0 X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 y x X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 y x X0
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op (M.op X1 X0) (M.op X2 X2))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op (M.op X1 X0) (M.op X2 X2)) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op y x) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq79
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq79
    | exact resolve eq79 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq85 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq84
    | exact resolve eq84 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq106 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k (τ X0) X1) X2
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq10
    | exact resolve eq10 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq16
    | exact resolve eq16 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq314 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq328 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq342 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X1 X1)
       have i₂ := eq54 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq361 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq328 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq328 X0 X1
       grind)
    | exact superpose eq328 eq12
    | (have j0 := eq12 X0 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq328 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq328 X1 X1
       grind)
    | exact resolve eq12 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq361 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq401 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq106 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq106
    | (have j0 := eq106 (σ X0)
       grind)
    | exact resolve eq106 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X0 (M.op X1 X1))) (M.op X3 X3))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X0 (M.op X1 X1)) X2 X3 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X0 X1
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq447 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X0) (M.op X3 X3)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X0 (M.op X4 X4))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X1 (M.op (M.op X1 X0) (M.op X3 X3)) X4 X2
       have i₂ := eq14 X0 X1 X3
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq448 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X3 X3)) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X1 (M.op X4 X4)) X5 X3
       have i₂ := eq53 X1 X0 X2 X4
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq449 : ∀ X0 X1 X2 : G, (M.op (M.op x y) (M.op X1 X1)) = (M.op (M.op x (M.op X0 X0)) (M.op y (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq450 : ∀ X0 X1 X2 : G, (M.op (M.op (σ x) (σ y)) (M.op X1 X1)) = (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ y) (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq461 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X2)) (M.op X0 X0)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 X1 (M.op X1 X1) X2
       have i₂ := eq54 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq54
  have eq553 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq566 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq553 X0
       have i₂ := eq342 (σ X0) (σ X0)
       grind)
    | exact superpose eq342 eq553
    | exact resolve eq553 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq574 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq566 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq566
    | exact resolve eq566 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq640 : ∀ X0 : G, (k (k x x) (τ X0)) = (τ (k (k (σ x) (σ x)) X0)) := by
    intro X0
    first
    | (have i₁ := eq314 (k x x) X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq314
    | exact resolve eq314 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq314
  have eq740 : ∀ X0 X1 : G, (k (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq574 X1
       have i₂ := eq328 X0 (σ X1)
       grind)
    | (have i₁ := eq574 X1
       have i₂ := eq328 (σ X1) X0
       grind)
    | exact superpose eq328 eq574
    | exact resolve eq574 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq845 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq73 X1 X0
       grind)
    | (have i₁ := eq12 (σ X1) (σ X1)
       have i₂ := eq73 X0 X1
       grind)
    | exact superpose eq73 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq73 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq73 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq73 X0 X0
       grind)
    | exact resolve eq12 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq865 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq845 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq866 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq865 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq865
  have eq871 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq866 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq866
    | (have j0 := eq866 X0 X1
       grind)
    | exact resolve eq866 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq905 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq39 X0 (τ (M.op X1 X1))
       have i₂ := eq740 X1 (τ X0)
       grind)
    | exact superpose eq740 eq39
    | exact resolve eq39 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq911 : ∀ X0 X1 : G, (σ (τ X0)) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq905 X0 X1
       have i₂ := eq15 (M.op X1 X1)
       grind)
    | exact superpose eq15 eq905
    | exact resolve eq905 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq914 : ∀ X0 X1 : G, (k (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq911 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq911
    | exact resolve eq911 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq2923 : ∀ X0 X1 : G, (σ (k (k (τ (σ X0)) X0) X1)) = (k (M.op (σ X0) (σ X0)) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq211 (σ X0) X0 X1
       have i₂ := eq106 (σ X0)
       grind)
    | exact superpose eq106 eq211
    | (have j1 := eq106 (σ X0)
       grind)
    | exact resolve eq211 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq211
  have eq3013 : ∀ X0 X1 : G, (σ X1) = (σ (k (k (τ (σ X0)) X0) X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2923 X0 X1
       have i₂ := eq914 (σ X1) (σ X0)
       grind)
    | exact superpose eq914 eq2923
    | (have j0 := eq2923 X0 X1
       grind)
    | exact resolve eq2923 eq914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914 eq2923
  have eq3034 : ∀ X0 X1 : G, (σ X1) = (σ (k (k X0 X0) X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3013 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq3013
    | (have j0 := eq3013 X0 X1
       grind)
    | exact resolve eq3013 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3013
  have eq4281 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) ∨ (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq740 X1 (τ (M.op X1 X1))
       have i₂ := eq372 X0 (τ (M.op X1 X1))
       grind)
    | exact superpose eq372 eq740
    | (have j1 := eq372 X0 (τ (M.op X1 X1))
       grind)
    | exact resolve eq740 eq372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq4321 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq372 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq4325 : ∀ X0 X1 : G, (M.op X0 X0) = (τ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq4281 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4281
  have eq4441 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (τ (M.op X0 X0))) x) := by
    intro X0
    first
    | (have i₁ := eq51 x
       have i₂ := eq4325 x X0
       grind)
    | exact superpose eq4325 eq51
    | exact resolve eq51 eq4325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4484 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X1 X1)
       have i₂ := eq4325 X0 X1
       grind)
    | exact superpose eq4325 eq15
    | exact resolve eq15 eq4325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4673 : ∀ X0 X2 : G, (M.op (σ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq342 x X2
       have i₂ := eq4484 X0 x
       grind)
    | exact superpose eq4484 eq342
    | exact resolve eq342 eq4484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4484
  have eq5253 : ∀ X0 X1 X3 : G, (M.op x (M.op X1 X1)) = (M.op y (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X3 X3))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq440 y x (M.op x (M.op X1 X1)) X3
       have i₂ := eq449 X1 X0 x
       grind)
    | exact superpose eq449 eq440
    | exact resolve eq440 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5259 : ∀ X1 : G, (M.op y (M.op x y)) = (M.op x (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq5253 x X1 x
       have i₂ := eq461 x sF0 x
       grind)
    | exact superpose eq461 eq5253
    | exact resolve eq5253 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5253
  have eq5408 : ∀ X0 X1 X3 : G, (M.op (σ x) (M.op X1 X1)) = (M.op (σ y) (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X3 X3))) := by
    intro X0 X1 X3
    first
    | exact superpose eq450 eq440
    | exact resolve eq440 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5414 : ∀ X1 : G, (M.op (σ x) (M.op X1 X1)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    intro X1
    first
    | (have i₁ := eq5408 x X1 x
       have i₂ := eq461 x sF4 x
       grind)
    | exact superpose eq461 eq5408
    | exact resolve eq5408 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5408
  have eq5612 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq328 X1 (σ X0)
       have i₂ := eq401 X0
       grind)
    | exact superpose eq401 eq328
    | (have j1 := eq401 X0
       grind)
    | exact resolve eq328 eq401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5649 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq401 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq6712 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op x (M.op X0 X0)) (M.op y (M.op X1 X1))) (M.op X3 X3)) = (M.op (M.op (M.op x y) (M.op X4 X4)) (M.op (M.op X2 X2) (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | exact superpose eq449 eq447
    | exact resolve eq447 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq6715 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ y) (M.op X1 X1))) (M.op X3 X3)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X4 X4)) (M.op (M.op X2 X2) (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | exact superpose eq450 eq447
    | exact resolve eq447 eq450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq6963 : ∀ X0 X1 X2 X3 X5 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op (M.op (M.op X0 X1) (M.op X2 X2)) (M.op X5 X5))) := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq440 X1 x (M.op X0 (M.op X3 X3)) X5
       have i₂ := eq447 X1 X0 X3 X2 x
       grind)
    | (have i₁ := eq440 (M.op X1 X1) X1 (M.op X1 X0) X3
       have i₂ := eq447 X0 X1 X2 (M.op X1 X1) x
       grind)
    | exact superpose eq447 eq440
    | exact resolve eq440 eq447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440 eq447
  have eq7097 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X3 X3)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq6963 X0 X1 x X3 x
       have i₂ := eq461 x (M.op X0 X1) x
       grind)
    | exact superpose eq461 eq6963
    | exact resolve eq6963 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6963
  have eq7188 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ y) (M.op X1 X1))) (M.op X3 X3)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op X4 X4)) (M.op X5 X5)) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq6715 X0 X1 x X3 X4 X5
       have i₂ := eq342 x (M.op X5 X5)
       grind)
    | exact superpose eq342 eq6715
    | exact resolve eq6715 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6715
  have eq7190 : ∀ X0 X1 X3 X4 X5 : G, (M.op (M.op (M.op x (M.op X0 X0)) (M.op y (M.op X1 X1))) (M.op X3 X3)) = (M.op (M.op (M.op x y) (M.op X4 X4)) (M.op X5 X5)) := by
    intro X0 X1 X3 X4 X5
    first
    | (have i₁ := eq6712 X0 X1 x X3 X4 X5
       have i₂ := eq342 x (M.op X5 X5)
       grind)
    | exact superpose eq342 eq6712
    | exact resolve eq6712 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6712
  have eq7246 : ∀ X0 X1 X3 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (M.op X0 X0)) (M.op (σ y) (M.op X1 X1))) (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq7188 X0 X1 X3 x X0
       have i₂ := eq461 X0 sF4 x
       grind)
    | exact superpose eq461 eq7188
    | exact resolve eq7188 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7188
  have eq7248 : ∀ X0 X1 X3 : G, (M.op x y) = (M.op (M.op (M.op x (M.op X0 X0)) (M.op y (M.op X1 X1))) (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq7190 X0 X1 X3 x X0
       have i₂ := eq461 X0 sF0 x
       grind)
    | exact superpose eq461 eq7190
    | exact resolve eq7190 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7190
  have eq7271 : ∀ X1 X3 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op X1 X1))) (M.op X3 X3)) := by
    intro X1 X3
    first
    | exact superpose eq5414 eq7246
    | exact resolve eq7246 eq5414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7246
  have eq7272 : ∀ X1 X3 : G, (M.op x y) = (M.op (M.op (M.op y (M.op x y)) (M.op y (M.op X1 X1))) (M.op X3 X3)) := by
    intro X1 X3
    first
    | (have i₁ := eq7248 x X1 X3
       have i₂ := eq5259 x
       grind)
    | exact superpose eq5259 eq7248
    | exact resolve eq7248 eq5259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5259 eq7248
  have eq7962 : ∀ X0 X1 X4 X5 : G, (M.op X1 (M.op X4 X4)) = (M.op (M.op X0 X1) (M.op X0 (M.op X5 X5))) := by
    intro X0 X1 X4 X5
    first
    | (have i₁ := eq448 X0 X1 x x X4 X5
       have i₂ := eq461 x (M.op X0 X1) x
       grind)
    | exact superpose eq461 eq448
    | exact resolve eq448 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq448 eq461
  have eq8345 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X3 X3))) X1) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X1 x
       have i₂ := eq7962 X0 (M.op X1 X2) x X3
       grind)
    | exact superpose eq7962 eq14
    | exact resolve eq14 eq7962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8365 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 (M.op x y)) (M.op X0 (M.op X1 X1))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq51 x
       have i₂ := eq7962 X0 sF0 x x
       grind)
    | exact superpose eq7962 eq51
    | exact resolve eq51 eq7962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq8372 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op X1 X1))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq52 x
       have i₂ := eq7962 X0 sF4 x x
       grind)
    | exact superpose eq7962 eq52
    | exact resolve eq52 eq7962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq7962
  have eq13533 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k (σ x) X0) = (M.op (σ x) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq871 (τ X0) x
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq871
    | (have j0 := eq871 (τ X0) x
       grind)
    | exact resolve eq871 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq871
  have eq13886 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (k (σ x) X0) = (M.op (σ x) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq13533 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13533
    | (have j0 := eq13533 X0
       grind)
    | exact resolve eq13533 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13533
  have eq13982 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (k (σ x) X0) = (M.op (σ x) (σ x)) ∨ (k (σ x) X0) = (M.op (σ x) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq13886 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq13886
    | (have j0 := eq13886 X0
       grind)
    | exact resolve eq13886 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13886
  have eq14072 : ∀ X0 : G, (M.op X0 X0) = (σ x) ∨ (k (σ x) X0) = (M.op (σ x) (σ x)) ∨ (k (σ x) X0) = (M.op (σ x) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq13982 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq13982
    | (have j0 := eq13982 X0
       grind)
    | exact resolve eq13982 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13982
  have eq14157 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (M.op X0 X0) = (σ x) ∨ (k (σ x) X0) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14072 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq14072
    | (have j0 := eq14072 X0
       grind)
    | exact resolve eq14072 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14072
  have eq14236 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ x) ∨ (k (σ x) X0) = (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq14157 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq14157
    | (have j0 := eq14157 X0
       grind)
    | exact resolve eq14157 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14157
  have eq36267 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X1 (M.op (σ x) (σ y))) (M.op X0 (M.op X1 X0))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq8372 X1 x
       have i₂ := eq7097 X1 X0 x
       grind)
    | (have i₁ := eq8372 X1 X1
       have i₂ := eq7097 X1 X1 x
       grind)
    | exact superpose eq7097 eq8372
    | exact resolve eq8372 eq7097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7097 eq8372
  have eq55805 : ∀ X0 X1 : G, (k (τ (σ X0)) X0) = X0 ∨ (M.op X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq574 X0
       have i₂ := eq5612 X0 X1
       grind)
    | exact superpose eq5612 eq574
    | (have j1 := eq5612 X0 X1
       grind)
    | exact resolve eq574 eq5612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq5612
  have eq56049 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (k X0 X0)) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq55805 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq55805
    | (have j0 := eq55805 X0 X1
       grind)
    | exact resolve eq55805 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55805
  have eq56718 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 (M.op y x)) (M.op X0 (M.op X1 X1))) y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq8345 X0 y y X1
       have i₂ := eq85
       grind)
    | exact superpose eq85 eq8345
    | exact resolve eq8345 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq56727 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq56718 x x
       have i₂ := eq8345 x y x x
       grind)
    | exact superpose eq8345 eq56718
    | exact resolve eq56718 eq8345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8345 eq56718
  have eq56935 : ∀ X0 : G, (σ (τ X0)) = (σ (τ (k (k (σ x) (σ x)) X0))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq3034 x (τ X0)
       have i₂ := eq640 X0
       grind)
    | exact superpose eq640 eq3034
    | (have j0 := eq3034 x x
       grind)
    | exact resolve eq3034 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640 eq3034
  have eq57168 : ∀ X0 : G, (σ (τ X0)) = (k (k (σ x) (σ x)) X0) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq56935 X0
       have i₂ := eq15 (k (k sF2 sF2) X0)
       grind)
    | exact superpose eq15 eq56935
    | exact resolve eq56935 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56935
  have eq57210 : ∀ X0 : G, (k (k (σ x) (σ x)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq57168 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq57168
    | exact resolve eq57168 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57168
  have eq57228 : ∀ X0 : G, (k (k (σ x) (σ x)) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq57210 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq57210
    | (have j0 := eq57210 X0
       grind)
    | exact resolve eq57210 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57210
  have eq58659 : ∀ X0 : G, (τ (σ X0)) = (k (τ (k (σ x) (σ x))) X0) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq57228 eq213
    | exact resolve eq213 eq57228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq57228
  have eq58708 : ∀ X0 : G, (τ (σ X0)) = (k (k x x) X0) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq50 eq58659
    | exact resolve eq58659 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq58659
  have eq58723 : ∀ X0 : G, (k (k x x) X0) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq58708 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq58708
    | exact resolve eq58708 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58708
  have eq65373 : ∀ X0 : G, (k x x) ≠ (k x x) ∨ (M.op X0 X0) = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq4321 X0 (k x x)
       have i₂ := eq58723 (k x x)
       grind)
    | exact superpose eq58723 eq4321
    | (have j0 := eq4321 X0 (k x x)
       grind)
    | (have r₁ := eq4321 X0 (k x x)
       have r₂ := eq58723 (k x x)
       grind)
    | exact resolve eq4321 eq58723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58723
  have eq65416 : ∀ X0 : G, (M.op X0 X0) = (k x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq65373 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65373
  have eq89404 : ∀ X0 : G, (σ x) ≠ (σ (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq5649 x
       have i₂ := eq65416 X0
       grind)
    | exact superpose eq65416 eq5649
    | (have j0 := eq5649 x
       grind)
    | exact resolve eq5649 eq65416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5649 eq65416
  have eq89423 : ∀ X0 : G, (σ x) ≠ (σ (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq89404 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq89404
    | (have j0 := eq89404 X0
       grind)
    | exact resolve eq89404 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89404
  have eq89528 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq89423 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq89423
    | (have j0 := eq89423 X0
       grind)
    | exact resolve eq89423 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89423
  have eq89529 : ∀ X0 : G, (σ x) ≠ (σ (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq89528 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89528
  have eq453783 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (k X0 X0))) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4325 X1 x
       have i₂ := eq56049 X0 x
       grind)
    | exact superpose eq56049 eq4325
    | (have j1 := eq56049 X0 X1
       grind)
    | exact resolve eq4325 eq56049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56049
  have eq455249 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X0) ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq453783 X0 X1
       have i₂ := eq16 (k X0 X0)
       grind)
    | exact superpose eq16 eq453783
    | (have j0 := eq453783 X0 X1
       grind)
    | exact resolve eq453783 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453783
  have eq469336 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 ∨ (k X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4321 X2 X1
       have i₂ := eq455249 X1 X0
       grind)
    | exact superpose eq455249 eq4321
    | (have j0 := eq4321 X2 X1
       have j1 := eq455249 X1 X1
       grind)
    | (have r₁ := eq4321 X0 (M.op X1 X1)
       have r₂ := eq455249 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq4321 X0 X0
       have r₂ := eq455249 X0 X1
       grind)
    | exact resolve eq4321 eq455249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455249
  have eq470349 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq469336 X0 X1 X2
       have j1 := eq4321 X2 X1
       grind)
    | (have r₁ := eq469336 X0 X1 X2
       have r₂ := eq4321 X0 X1
       grind)
    | (have r₁ := eq469336 X0 (M.op X0 X0) X2
       have r₂ := eq4321 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq469336 X0 (k (M.op X2 X2) (M.op X2 X2)) X2
       have r₂ := eq4321 X0 (M.op X2 X2)
       grind)
    | exact resolve eq469336 eq4321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4321 eq469336
  have eq577908 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq56727 eq14236
    | (have j0 := eq14236 (σ y)
       grind)
    | exact resolve eq14236 eq56727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14236 eq56727
  have eq577914 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq577908
    | exact resolve eq577908 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq577908
  have eq577927 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq577914
       have r₂ := eq28
       grind)
    | exact resolve eq577914 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577914
  have eq580864 : ∀ X0 : G, (M.op X0 X0) = (τ (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq577927 eq4325
    | exact resolve eq4325 eq577927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4325 eq577927
  have eq581442 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq580864
    | exact resolve eq580864 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq580864
  have eq581467 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have j0 := eq581442 y
       have j1 := eq470349 x (σ (M.op x y)) (σ x)
       grind)
    | (have r₁ := eq581442 x
       have r₂ := eq470349 x x x
       grind)
    | (have r₁ := eq581442 x
       have r₂ := eq470349 (σ x) (σ (M.op x y)) x
       grind)
    | (have r₁ := eq581442 x
       have r₂ := eq470349 y x x
       grind)
    | exact resolve eq581442 eq470349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470349 eq581442
  have eq581534 : y = (M.op (M.op (M.op x y) (τ (σ (M.op x y)))) x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq581467 eq4441
    | exact resolve eq4441 eq581467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4441 eq581467
  have eq582088 : y = (M.op (M.op (M.op x y) (M.op x y)) x) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq31 eq581534
    | exact resolve eq581534 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq581534
  have eq582119 : x = y ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq582088
       have i₂ := eq342 sF0 x
       grind)
    | exact superpose eq342 eq582088
    | exact resolve eq582088 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582088
  have eq582120 : x = (M.op y y) ∨ x = y := by grind
  clear eq582119
  have eq582397 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op y (M.op x y)) (M.op y (M.op X0 X0))) x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq7272 X0 y
       have i₂ := eq582120
       grind)
    | exact superpose eq582120 eq7272
    | exact resolve eq7272 eq582120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7272
  have eq582540 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq89529 y
       have i₂ := eq582120
       grind)
    | exact superpose eq582120 eq89529
    | exact resolve eq89529 eq582120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89529 eq582120
  have eq582666 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | (have r₁ := eq582540
       have r₂ := eq23
       grind)
    | exact resolve eq582540 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582540
  have eq582698 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq8365 eq582397
    | exact resolve eq582397 eq8365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8365 eq582397
  have eq585653 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq582698 eq21
    | exact resolve eq21 eq582698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582698
  have eq586096 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq585653
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq585653
    | exact resolve eq585653 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585653
  have eq594440 : (σ y) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) (σ x)) ∨ x = y := by
    first
    | exact superpose eq582666 eq36267
    | exact resolve eq36267 eq582666
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36267 eq582666
  have eq594451 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq594440
       have i₂ := eq14 sF4 sF2 sF2
       grind)
    | exact superpose eq14 eq594440
    | exact resolve eq594440 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594440
  have eq594857 : (σ (M.op x y)) ≠ (σ y) ∨ x = y := by
    first
    | exact superpose eq594451 eq28
    | exact resolve eq28 eq594451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594451
  have eq594958 : x = y := by
    first
    | (have r₁ := eq594857
       have r₂ := eq586096
       grind)
    | exact resolve eq594857 eq586096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq586096 eq594857
  have eq594960 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq594958
       grind)
    | exact superpose eq594958 eq19
    | exact resolve eq19 eq594958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq594961 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq594958
       grind)
    | exact superpose eq594958 eq25
    | exact resolve eq25 eq594958
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq594958
  have eq595366 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq594961
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq594961
    | exact resolve eq594961 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq594961
  have eq595725 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq594960
       have i₂ := eq328 X0 x
       grind)
    | (have i₁ := eq594960
       have i₂ := eq328 x X0
       grind)
    | exact superpose eq328 eq594960
    | exact resolve eq594960 eq328
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328
  have eq596004 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (σ y) (M.op X0 X0))) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq7271 X0 x
       have i₂ := eq594960
       grind)
    | exact superpose eq594960 eq7271
    | exact resolve eq7271 eq594960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7271 eq594960
  have eq596384 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op X0 X0))) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq595366 eq596004
    | exact resolve eq596004 eq595366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq596004
  have eq596572 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op x y)) := by
    first
    | exact superpose eq5414 eq596384
    | exact resolve eq596384 eq5414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5414 eq596384
  have eq596644 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (σ x) (M.op (σ x) (σ y)))) (M.op x y)) := by
    first
    | exact superpose eq595366 eq596572
    | exact resolve eq596572 eq595366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595366 eq596572
  have eq596686 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq596644
       have i₂ := eq342 (M.op sF2 sF4) sF0
       grind)
    | exact superpose eq342 eq596644
    | exact resolve eq596644 eq342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342 eq596644
  have eq596700 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq596686 eq28
    | exact resolve eq28 eq596686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq596686
  have eq598123 : ∀ X0 : G, (M.op x y) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4673 X0 (σ (M.op X0 X0))
       have i₂ := eq595725 (σ (M.op X0 X0))
       grind)
    | exact superpose eq595725 eq4673
    | exact resolve eq4673 eq595725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4673
  have eq598249 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq598123 x
       have i₂ := eq595725 x
       grind)
    | exact superpose eq595725 eq598123
    | exact resolve eq598123 eq595725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595725 eq598123
  have eq599338 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq21 eq598249
    | exact resolve eq598249 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq598249
  have eq600836 : False := by grind
  exact eq600836

/-- `Equation2725`: `x = ((y ◇ x) ◇ (z ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_Equation2725 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2725 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2725.models_iff G M).mp hM
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X2 X2)) X1) = X0 := by
    intro X0 X1 X2
    grind
  have eq15 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
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
  have eq32 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq22 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq40 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq45 : (σ (k x x)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq24
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
  have eq55 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X2) (M.op (M.op X1 X1) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq101 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
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
  clear eq46
  have eq107 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq101
    | exact resolve eq101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq22 eq107
    | exact resolve eq107 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq218 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k (τ X0) X1)
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq16
    | exact resolve eq16 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq336 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X0 X0
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq347 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X1 X1)
       have i₂ := eq55 (M.op X1 X1) X1 X0
       grind)
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq495 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X0)) = (σ (k X2 X2)) ∨ (M.op X0 (M.op (M.op X1 X1) X0)) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq74 X0
       have i₂ := eq55 X0 X1 (σ X0)
       grind)
    | exact superpose eq55 eq74
    | exact resolve eq74 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq504 : ∀ X0 X1 X2 : G, (σ (k X0 X0)) = (M.op X1 (M.op (M.op X2 X2) X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 X2 (σ X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq55
    | (have j1 := eq74 X0
       grind)
    | exact resolve eq55 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq509 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq74 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq510 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq504 X0 X1 x
       have i₂ := eq347 x X1
       grind)
    | exact superpose eq347 eq504
    | (have j0 := eq504 X0 X1 x
       grind)
    | exact resolve eq504 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504
  have eq512 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (k X2 X2)) ∨ (M.op X0 (M.op (M.op X1 X1) X0)) = (σ X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq495 X0 X1 X2
       have i₂ := eq347 X1 X0
       grind)
    | exact superpose eq347 eq495
    | (have j0 := eq495 X0 X1 X2
       grind)
    | exact resolve eq495 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq518 : ∀ X0 X2 : G, (M.op X0 X0) = (σ (k X2 X2)) ∨ (M.op X0 X0) = (σ X2) := by
    intro X0 X2
    first
    | (have i₁ := eq512 X0 x X2
       have i₂ := eq347 x X0
       grind)
    | exact superpose eq347 eq512
    | (have j0 := eq512 X0 x X2
       grind)
    | exact resolve eq512 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq582 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq595 : ∀ X0 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq582 X0
       have i₂ := eq347 (σ X0) (σ X0)
       grind)
    | exact superpose eq347 eq582
    | exact resolve eq582 eq347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq603 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq595 X0
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq595
    | exact resolve eq595 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq819 : ∀ X0 X1 : G, (k (τ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq603 X1
       have i₂ := eq336 X0 (σ X1)
       grind)
    | (have i₁ := eq603 X1
       have i₂ := eq336 (σ X1) X0
       grind)
    | exact superpose eq336 eq603
    | exact resolve eq603 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq898 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (τ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq218 (τ (M.op X1 X1)) X0
       have i₂ := eq819 X1 (σ X0)
       grind)
    | exact superpose eq819 eq218
    | exact resolve eq218 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq900 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ (M.op X1 X1))) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0 (τ (M.op X1 X1))
       have i₂ := eq819 X1 (τ X0)
       grind)
    | exact superpose eq819 eq40
    | exact resolve eq40 eq819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq819
  have eq906 : ∀ X0 X1 : G, (σ (τ X0)) = (k (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq900 X0 X1
       have i₂ := eq15 (M.op X1 X1)
       grind)
    | exact superpose eq15 eq900
    | exact resolve eq900 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq900
  have eq907 : ∀ X0 X1 : G, (k (τ (τ (M.op X1 X1))) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq898 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq898
    | exact resolve eq898 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq910 : ∀ X0 X1 : G, (k (M.op X1 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq906 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq906
    | exact resolve eq906 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq2907 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq518 X1 (M.op X0 X0)
       have i₂ := eq910 (M.op X0 X0) X0
       grind)
    | exact superpose eq910 eq518
    | (have j0 := eq518 X1 (M.op X0 X0)
       grind)
    | exact resolve eq518 eq910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq910
  have eq2913 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) ∨ (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq518 X1 (τ (τ (M.op X0 X0)))
       have i₂ := eq907 (τ (τ (M.op X0 X0))) X0
       grind)
    | exact superpose eq907 eq518
    | (have j0 := eq518 X1 (τ (τ (M.op X0 X0)))
       grind)
    | exact resolve eq518 eq907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq907
  have eq2988 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have j0 := eq2913 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2913
  have eq2994 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq2907 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2907
  have eq3030 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2988 X0 X1
       have i₂ := eq15 (τ (M.op X0 X0))
       grind)
    | exact superpose eq15 eq2988
    | exact resolve eq2988 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2988
  have eq3085 : ∀ X0 X2 : G, (M.op (σ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq347 x X2
       have i₂ := eq2994 X0 x
       grind)
    | exact superpose eq2994 eq347
    | exact resolve eq347 eq2994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3196 : ∀ X0 X2 : G, (M.op (τ (M.op X0 X0)) X2) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq347 x X2
       have i₂ := eq3030 X0 x
       grind)
    | exact superpose eq3030 eq347
    | exact resolve eq347 eq3030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3030
  have eq5582 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq509 (τ X0)
       have i₂ := eq36 X0 (τ X0)
       grind)
    | exact superpose eq36 eq509
    | (have j0 := eq509 (τ X0)
       grind)
    | exact resolve eq509 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq509
  have eq5598 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5582 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5582
    | (have j0 := eq5582 X0
       grind)
    | exact resolve eq5582 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5582
  have eq5608 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5598 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5598
    | (have j0 := eq5598 X0
       grind)
    | exact resolve eq5598 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5598
  have eq5676 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ (k x x)) := by
    intro X0
    first
    | (have i₁ := eq510 x X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq510
    | (have j0 := eq510 x X0
       grind)
    | exact resolve eq510 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq5758 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq5676 X0
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq5676
    | exact resolve eq5676 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq5676
  have eq26991 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq5758 eq5608
    | (have j0 := eq5608 (σ x)
       grind)
    | exact resolve eq5608 eq5758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5608 eq5758
  have eq26993 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq26991 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26991
  have eq27070 : ∀ X0 : G, (σ x) ≠ (σ (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq26993 x
       have i₂ := eq2994 X0 x
       grind)
    | exact superpose eq2994 eq26993
    | exact resolve eq26993 eq2994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2994
  have eq30312 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq108 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq30313 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq28 eq30312
    | exact resolve eq30312 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30312
  have eq30318 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq30313
       have r₂ := eq29
       grind)
    | exact resolve eq30313 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30313
  have eq30320 : ∀ X0 : G, x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq30318
       have i₂ := eq336 X0 sF3
       grind)
    | (have i₁ := eq30318
       have i₂ := eq336 sF3 x
       grind)
    | exact superpose eq336 eq30318
    | exact resolve eq30318 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30318
  have eq30827 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq27070 y
       have i₂ := eq30320 X0
       grind)
    | exact superpose eq30320 eq27070
    | (have j1 := eq30320 (σ x)
       grind)
    | exact resolve eq27070 eq30320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27070 eq30320
  have eq30854 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq30827 (σ x)
       grind)
    | (have r₁ := eq30827 x
       have r₂ := eq26993 (σ x)
       grind)
    | (have r₁ := eq30827 x
       have r₂ := eq26993 x
       grind)
    | exact resolve eq30827 eq26993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26993 eq30827
  have eq30895 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq30854
       have r₂ := eq24
       grind)
    | exact resolve eq30854 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30854
  have eq30912 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq30895 eq347
    | exact resolve eq347 eq30895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq30958 : ∀ X0 : G, (M.op (τ (σ x)) X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq30895 eq3196
    | exact resolve eq3196 eq30895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3196 eq30895
  have eq31069 : ∀ X0 : G, (M.op x X0) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq30 eq30958
    | exact resolve eq30958 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30958
  have eq31763 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq28 eq30912
    | (have j0 := eq30912 (σ y)
       grind)
    | exact resolve eq30912 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30912
  have eq32029 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq31763 eq29
    | exact resolve eq29 eq31763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31763
  have eq32483 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq31069 y
       have i₂ := eq20
       grind)
    | exact superpose eq20 eq31069
    | (have j0 := eq31069 y
       grind)
    | exact resolve eq31069 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31069
  have eq32956 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32483 eq31
    | exact resolve eq31 eq32483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq32483
  have eq33022 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq32956
    | exact resolve eq32956 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32956
  have eq33023 : y = (M.op x y) ∨ x = y := by grind
  clear eq33022
  have eq33025 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq33023 eq22
    | exact resolve eq22 eq33023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33171 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq33025
       have i₂ := eq26
       grind)
    | exact superpose eq26 eq33025
    | exact resolve eq33025 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33025
  have eq33222 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq33171 eq32029
    | (have r₁ := eq32029
       have r₂ := eq33171
       grind)
    | exact resolve eq32029 eq33171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32029 eq33171
  have eq33225 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq33222
  have eq33226 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq33225
  have eq33398 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq33226 eq30
    | exact resolve eq30 eq33226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq33226
  have eq33478 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32 eq33398
    | exact resolve eq33398 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq33398
  have eq33562 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq33478 eq33023
    | exact resolve eq33023 eq33478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33023 eq33478
  have eq33563 : x = y := by grind
  clear eq33562
  have eq33628 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq20
       have i₂ := eq33563
       grind)
    | exact superpose eq33563 eq20
    | exact resolve eq20 eq33563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq33629 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq33563
       grind)
    | exact superpose eq33563 eq26
    | exact resolve eq26 eq33563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq33563
  have eq33754 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq33629
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq33629
    | exact resolve eq33629 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq33629
  have eq33761 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq33754 eq28
    | exact resolve eq28 eq33754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq33754
  have eq33844 : ∀ X0 : G, (M.op X0 X0) = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq33628
       have i₂ := eq336 X0 x
       grind)
    | (have i₁ := eq33628
       have i₂ := eq336 x X0
       grind)
    | exact superpose eq336 eq33628
    | exact resolve eq33628 eq336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336 eq33628
  have eq34356 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq33761 eq33844
    | exact resolve eq33844 eq33761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33761
  have eq34564 : ∀ X0 : G, (M.op x y) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3085 X0 (σ (M.op X0 X0))
       have i₂ := eq33844 (σ (M.op X0 X0))
       grind)
    | exact superpose eq33844 eq3085
    | exact resolve eq3085 eq33844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3085
  have eq34596 : (M.op x y) = (σ (M.op x y)) := by
    first
    | (have i₁ := eq34564 x
       have i₂ := eq33844 x
       grind)
    | exact superpose eq33844 eq34564
    | exact resolve eq34564 eq33844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33844 eq34564
  have eq34792 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq22 eq34596
    | exact resolve eq34596 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq34596
  have eq34903 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq34356 eq29
    | exact resolve eq29 eq34356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq34356
  have eq34996 : False := by grind
  exact eq34996

/-- `Equation2755`: `x = ((y ◇ y) ◇ (z ◇ x)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxx_pyy_pxy_Equation2755 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2755 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2755.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X0)) X2) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq44 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X1) (M.op X0 X1)) X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq44 (M.op X1 X0) X1
       have i₂ := eq44 X1 X0
       grind)
    | exact superpose eq44 eq44
    | exact resolve eq44 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X0 X0)
       have i₂ := eq44 (M.op X0 X0) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq44 eq9
    | exact resolve eq9 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X0) X0 X1
       have i₂ := eq46 (M.op X0 X0) X1
       grind)
    | exact superpose eq46 eq9
    | exact resolve eq9 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq46 (M.op X1 X1) X0
       have i₂ := eq49 X1 (M.op X0 (M.op X1 X1))
       grind)
    | exact superpose eq49 eq46
    | exact resolve eq46 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 X1
       have i₂ := eq23 X1
       grind)
    | exact superpose eq23 eq93
    | (have j0 := eq93 X0 X1
       grind)
    | exact resolve eq93 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq125 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 X1 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq65
    | exact resolve eq65 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq127 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X1 (σ X0)
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq55
    | exact resolve eq55 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq128 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq49 (σ X0) X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq49
    | exact resolve eq49 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq271 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq128 X0 (σ (M.op X1 X1))
       have i₂ := eq125 X1 (σ (M.op X0 X0))
       grind)
    | exact superpose eq125 eq128
    | exact resolve eq128 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125 eq128
  have eq306 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq95 x y
       grind)
    | exact superpose eq95 eq16
    | (have j1 := eq95 x y
       grind)
    | exact resolve eq16 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq369 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq127 X1 X0
       grind)
    | exact superpose eq127 eq10
    | exact resolve eq10 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5483 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq306
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq306
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq306
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq306
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq306 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq306
  have eq5484 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq5483
  have eq41225 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5484
       grind)
    | exact superpose eq5484 eq16
    | exact resolve eq16 eq5484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5484
  have eq41226 : (σ x) = (σ y) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq41225
       have r₂ := eq127 x (σ x)
       grind)
    | exact resolve eq41225 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41225
  have eq531547 : y = (τ (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq41226
       grind)
    | exact superpose eq41226 eq10
    | exact resolve eq10 eq41226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41226
  have eq531850 : x = y ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq531547
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq531547
    | exact resolve eq531547 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531547
  have eq531852 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq531850
       grind)
    | exact superpose eq531850 eq16
    | exact resolve eq16 eq531850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531850
  have eq531853 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq531852
       have r₂ := eq127 x (σ x)
       grind)
    | exact resolve eq531852 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq531852
  have eq532061 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq531853
       grind)
    | exact superpose eq531853 eq10
    | exact resolve eq10 eq531853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531853
  have eq532438 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq532061
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq532061
    | exact resolve eq532061 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532061
  have eq532439 : x = (M.op y y) := by grind
  clear eq532438
  have eq533418 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 y X0
       have i₂ := eq532439
       grind)
    | exact superpose eq532439 eq49
    | exact resolve eq49 eq532439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq533435 : ∀ X0 : G, (σ x) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq271 y X0
       have i₂ := eq532439
       grind)
    | exact superpose eq532439 eq271
    | exact resolve eq271 eq532439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq533439 : ∀ X0 : G, (M.op X0 X0) = (τ x) := by
    intro X0
    first
    | (have i₁ := eq369 y X0
       have i₂ := eq532439
       grind)
    | exact superpose eq532439 eq369
    | exact resolve eq369 eq532439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq533984 : y = (M.op x y) := by
    first
    | (have i₁ := eq44 y y
       have i₂ := eq532439
       grind)
    | exact superpose eq532439 eq44
    | exact resolve eq44 eq532439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq532439
  have eq534119 : (σ x) = (σ (τ x)) := by
    first
    | (have i₁ := eq533435 x
       have i₂ := eq533439 x
       grind)
    | exact superpose eq533439 eq533435
    | exact resolve eq533435 eq533439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533435 eq533439
  have eq534207 : x = (σ x) := by
    first
    | (have i₁ := eq534119
       have i₂ := eq11 x
       grind)
    | exact superpose eq11 eq534119
    | exact resolve eq534119 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534119
  have eq534345 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq534207
       grind)
    | exact superpose eq534207 eq16
    | exact resolve eq16 eq534207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534207
  have eq534872 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq534345
       have i₂ := eq533418 (σ y)
       grind)
    | exact superpose eq533418 eq534345
    | exact resolve eq534345 eq533418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533418 eq534345
  have eq535108 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq534872
       have i₂ := eq533984
       grind)
    | exact superpose eq533984 eq534872
    | exact resolve eq534872 eq533984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533984 eq534872
  have eq535109 : False := by grind
  exact eq535109
