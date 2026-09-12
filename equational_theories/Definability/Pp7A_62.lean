import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3296`: `x ◇ x = y ◇ (z ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then Y else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_y_pyy_pxy_Equation3296 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3296 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3296.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = b :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X2 (M.op X2 X0))) := by
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
  have eq61 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op x (M.op x y))) := by
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
  have eq62 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) X0 (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))) = (M.op X2 (M.op X3 (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 (M.op X1 X0)) X2 X3
       have i₂ := eq14 X0 X3 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X1
       have i₂ := eq14 X0 X1 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X2 X3 : G, (M.op X0 X0) = (M.op X2 (M.op X3 (M.op X0 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq64 X0 x X2 X3
       have i₂ := eq14 X0 (M.op x (M.op x X0)) x
       grind)
    | (have i₁ := eq64 X0 x X2 X3
       have i₂ := eq14 (M.op x (M.op x X0)) x X2
       grind)
    | exact superpose eq14 eq64
    | exact resolve eq64 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
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
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq86
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq86
    | exact resolve eq86 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq96 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq94
    | exact resolve eq94 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq97 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq96
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq96
    | exact resolve eq96 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq109 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq215 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 (M.op y y)) := by
    intro X0
    first
    | exact superpose eq61 eq14
    | exact resolve eq14 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 : G, (M.op y y) ≠ (M.op x (M.op x y)) ∨ (M.op x (M.op x y)) = (k X0 (M.op x (M.op x y))) := by
    intro X0
    first
    | exact superpose eq61 eq13
    | (have j0 := eq13 X0 (M.op x (M.op x y))
       grind)
    | exact resolve eq13 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ y) (σ y))) := by
    intro X0
    first
    | exact superpose eq62 eq14
    | exact resolve eq14 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 (M.op X1 X0) X1 X2
       have i₂ := eq14 X0 (M.op X1 (M.op X1 X0)) X1
       grind)
    | exact superpose eq14 eq65
    | exact resolve eq65 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq62 eq65
    | exact resolve eq65 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq436 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 X1)) (M.op X2 (M.op X3 X1))) = (M.op X4 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq65 (M.op X3 X1) X2 X4
       have i₂ := eq65 X1 X3 X0
       grind)
    | (have i₁ := eq65 (M.op X0 X0) X1 X2
       have i₂ := eq65 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq65 eq65
    | exact resolve eq65 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 y) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq65 y X0 x
       have i₂ := eq215 x
       grind)
    | exact superpose eq215 eq65
    | exact resolve eq65 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op X0 (σ y)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq221 eq65
    | exact resolve eq65 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq470 : ∀ X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X3 X1)) (M.op X2 (M.op X3 X1))) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq436 x X1 X2 X3 x
       have i₂ := eq69 X1 x x
       grind)
    | (have i₁ := eq436 x X1 X2 X3 (M.op x (M.op X1 X1))
       have i₂ := eq69 (M.op x (M.op X1 X1)) X2 X3
       grind)
    | exact superpose eq69 eq436
    | exact resolve eq436 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq436
  have eq503 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq425 (M.op sF4 sF4)
       have i₂ := eq65 sF4 sF4 x
       grind)
    | (have i₁ := eq425 x
       have i₂ := eq65 sF4 x x
       grind)
    | exact superpose eq65 eq425
    | exact resolve eq425 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq425
  have eq1526 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq79 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq1527 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1526 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526
  have eq6625 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1527 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq1527
    | (have j0 := eq1527 (τ X0)
       grind)
    | exact resolve eq1527 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq6633 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6625 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6625
    | (have j0 := eq6625 X0
       grind)
    | exact resolve eq6625 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6625
  have eq6639 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6633 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq6633
    | (have j0 := eq6633 X0
       grind)
    | exact resolve eq6633 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6633
  have eq8460 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq97 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8461 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq8460
    | exact resolve eq8460 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8460
  have eq8472 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq8461
       have r₂ := eq27
       grind)
    | exact resolve eq8461 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8461
  have eq8474 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq8472
    | exact resolve eq8472 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8472
  have eq8479 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq8474 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq8474
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq8474
       grind)
    | exact resolve eq13 eq8474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8474
  have eq8502 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq8479 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8479
  have eq8786 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq8502 eq109
    | exact resolve eq109 eq8502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq8502
  have eq8829 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq8786
    | exact resolve eq8786 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq8786
  have eq8858 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq6639 y
       grind)
    | (have r₁ := eq8829
       have r₂ := eq6639 y
       grind)
    | exact resolve eq8829 eq6639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6639 eq8829
  have eq8974 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq215 X0
       have i₂ := eq8858
       grind)
    | exact superpose eq8858 eq215
    | exact resolve eq215 eq8858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8996 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op X0 y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq470 y x y
       have i₂ := eq8858
       grind)
    | exact superpose eq8858 eq470
    | exact resolve eq470 eq8858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8858
  have eq9003 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8996 x
       have i₂ := eq439 x
       grind)
    | (have i₁ := eq8996 x
       have i₂ := eq439 x
       grind)
    | exact superpose eq439 eq8996
    | (have j0 := eq8996 x
       grind)
    | exact resolve eq8996 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8996
  have eq10749 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8974 eq9003
    | exact resolve eq9003 eq8974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8974 eq9003
  have eq10806 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq10749 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10749
  have eq10897 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq10806 x
       grind)
    | exact superpose eq10806 eq18
    | (have j1 := eq10806 x
       grind)
    | exact resolve eq18 eq10806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10806
  have eq10900 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq10897
  have eq10924 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10900 eq27
    | exact resolve eq27 eq10900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10925 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10900 eq62
    | exact resolve eq62 eq10900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq10928 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op X0 (σ y)) (M.op X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10900 eq503
    | exact resolve eq503 eq10900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq10934 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq440 eq10928
    | (have j0 := eq10928 (σ x)
       grind)
    | exact resolve eq10928 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440 eq10928
  have eq10936 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq10925
    | (have j0 := eq10925 X0
       grind)
    | exact resolve eq10925 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10925
  have eq11013 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq10900 eq10936
    | exact resolve eq10936 eq10900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11088 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq11013 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11013
  have eq11158 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq11088 eq10936
    | exact resolve eq10936 eq11088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10936 eq11088
  have eq11218 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq11158 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11158
  have eq11363 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq11218
    | (have j0 := eq11218 (σ x) X0
       grind)
    | exact resolve eq11218 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11218
  have eq11564 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11363 eq10934
    | exact resolve eq10934 eq11363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10934 eq11363
  have eq11570 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11564
  have eq11618 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq11570 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | exact resolve eq13 eq11570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11570
  have eq11670 : ∀ X0 : G, (σ y) = (k X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq11618 X0
       grind)
    | (have r₁ := eq11618 X0
       have r₂ := eq10900
       grind)
    | exact resolve eq11618 eq10900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10900 eq11618
  have eq11876 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11670 eq97
    | exact resolve eq97 eq11670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq11670
  have eq11914 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq11876
  have eq11934 : y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11914
       have r₂ := eq10924
       grind)
    | exact resolve eq11914 eq10924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10924 eq11914
  have eq12975 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq215 X0
       have i₂ := eq11934
       grind)
    | exact superpose eq11934 eq215
    | exact resolve eq215 eq11934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq12999 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op X0 y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq470 y x y
       have i₂ := eq11934
       grind)
    | exact superpose eq11934 eq470
    | exact resolve eq470 eq11934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470 eq11934
  have eq13012 : y = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12999 x
       have i₂ := eq439 x
       grind)
    | (have i₁ := eq12999 x
       have i₂ := eq439 x
       grind)
    | exact superpose eq439 eq12999
    | (have j0 := eq12999 x
       grind)
    | exact resolve eq12999 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439 eq12999
  have eq16095 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq12975 eq13012
    | exact resolve eq13012 eq12975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12975 eq13012
  have eq16158 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq16095 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16095
  have eq16267 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq16158 x
       grind)
    | exact superpose eq16158 eq18
    | (have j1 := eq16158 x
       grind)
    | exact resolve eq18 eq16158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16158
  have eq16270 : y = (M.op x y) := by grind
  clear eq16267
  have eq16302 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq16270 eq20
    | exact resolve eq20 eq16270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq16305 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq16270 eq61
    | exact resolve eq61 eq16270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq16412 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16305 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16305
    | (have j0 := eq16305 X0
       grind)
    | exact resolve eq16305 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16305
  have eq16415 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq16302
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16302
    | exact resolve eq16302 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16302
  have eq16416 : ∀ X0 : G, (M.op y y) = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq16270 eq16412
    | exact resolve eq16412 eq16270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16412
  have eq16417 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq16415 eq26
    | exact resolve eq26 eq16415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq16971 : ∀ X0 X1 : G, (M.op X1 y) = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq16416 X0
       have i₂ := eq16416 X1
       grind)
    | (have i₁ := eq16416 X0
       have i₂ := eq16416 y
       grind)
    | exact superpose eq16416 eq16416
    | exact resolve eq16416 eq16416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16416
  have eq17206 : ∀ X0 X1 : G, (M.op x (M.op x y)) ≠ (M.op X0 y) ∨ (M.op x (M.op x y)) = (k X1 (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq216 X1
       have i₂ := eq16971 X0 y
       grind)
    | (have i₁ := eq216 X1
       have i₂ := eq16971 y X0
       grind)
    | exact superpose eq16971 eq216
    | (have j0 := eq216 X1
       grind)
    | exact resolve eq216 eq16971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq17209 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x (M.op x y)) = (k X1 (M.op x (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq16270 eq17206
    | (have j0 := eq17206 X0 X1
       grind)
    | exact resolve eq17206 eq16270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17206
  have eq17232 : ∀ X1 : G, (M.op x (M.op x y)) = (k X1 (M.op x (M.op x y))) := by
    intro X1
    first
    | (have j0 := eq17209 x X1
       grind)
    | (have r₁ := eq17209 x X1
       have r₂ := eq16971 x x
       grind)
    | (have r₁ := eq17209 X1 X1
       have r₂ := eq16971 x X1
       grind)
    | exact resolve eq17209 eq16971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16971 eq17209
  have eq17244 : ∀ X1 : G, (M.op x y) = (k X1 (M.op x y)) := by
    intro X1
    first
    | exact superpose eq16270 eq17232
    | exact resolve eq17232 eq16270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17232
  have eq17248 : ∀ X1 : G, (M.op x y) = (k X1 (M.op x y)) := by
    intro X1
    first
    | (have i₁ := eq17244 X1
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq17244
    | (have j0 := eq17244 X1
       grind)
    | exact resolve eq17244 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq17244
  have eq17250 : ∀ X1 : G, y = (k X1 y) := by
    intro X1
    first
    | exact superpose eq16270 eq17248
    | exact resolve eq17248 eq16270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16270 eq17248
  have eq17421 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1527 y
       have i₂ := eq17250 y
       grind)
    | exact superpose eq17250 eq1527
    | (have j0 := eq1527 y
       grind)
    | exact resolve eq1527 eq17250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1527 eq17250
  have eq17438 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq17421
  have eq17450 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq17438
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq17438
    | exact resolve eq17438 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq17438
  have eq17493 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq16415 eq17450
    | exact resolve eq17450 eq16415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16415 eq17450
  have eq17772 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq17493 eq420
    | exact resolve eq420 eq17493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq17797 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq17493 eq17772
    | exact resolve eq17772 eq17493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17493 eq17772
  have eq17857 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17797 eq16417
    | exact resolve eq16417 eq17797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16417 eq17797
  have eq17861 : False := by grind
  exact eq17861

/-- `Equation335`: `x ◇ y = y ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_x_pyx_pxx_pyx_Equation335 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law335 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law335.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
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
  have eq34 : (M.op y x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : (M.op (σ y) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : (M.op x y) = (M.op y (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq14 x y
       have i₂ := eq34
       grind)
    | exact superpose eq34 eq14
    | exact resolve eq14 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : (M.op x y) = (M.op y (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq37
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq37
    | exact resolve eq37 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq39 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq35 eq14
    | exact resolve eq14 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq26 eq39
    | exact resolve eq39 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq41 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq42 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq43 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq45 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq53 : (σ (k x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq42 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq42
    | (have j0 := eq42 y
       grind)
    | exact resolve eq42 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq62 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq53
       grind)
    | exact superpose eq53 eq16
    | exact resolve eq16 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq89 : (σ (k y x)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq43 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq43
    | (have j0 := eq43 x
       grind)
    | exact resolve eq43 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq90 : (σ (k y y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq43 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43
    | (have j0 := eq43 y
       grind)
    | exact resolve eq43 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq89
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq89
    | (have j1 := eq67 y x
       grind)
    | exact resolve eq89 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq100
    | exact resolve eq100 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq101
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq101
    | exact resolve eq101 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq128 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq102 eq67
    | (have j0 := eq67 (σ y) (σ x)
       grind)
    | exact resolve eq67 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq129 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq128
    | exact resolve eq128 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq132 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq129
       have r₂ := eq27
       grind)
    | exact resolve eq129 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq134 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq132
    | exact resolve eq132 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq148 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134 eq40
    | exact resolve eq40 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq148
    | exact resolve eq148 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq163 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134 eq150
    | exact resolve eq150 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq165 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq150 eq14
    | exact resolve eq14 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq166 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq163
  have eq169 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op (σ y) X0) = (k X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq166 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq166
       grind)
    | exact resolve eq13 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 : G, (M.op (σ y) X0) = (k X0 (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq169 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq172 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq165 eq14
    | exact resolve eq14 eq165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : (k x y) = (τ (M.op (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq170 eq62
    | exact resolve eq62 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq189 : (k x y) = (τ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35 eq187
    | exact resolve eq187 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq190 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134 eq189
    | exact resolve eq189 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq192 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq190
  have eq194 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq192
    | exact resolve eq192 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192
  have eq196 : (k (σ x) (σ y)) = (σ (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq53
       have i₂ := eq194
       grind)
    | exact superpose eq194 eq53
    | exact resolve eq53 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq199 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq196
       have i₂ := eq15 sF4
       grind)
    | exact superpose eq15 eq196
    | exact resolve eq196 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq218 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq199 eq170
    | exact resolve eq170 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq218
  have eq223 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35 eq220
    | exact resolve eq220 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq230 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq223 eq40
    | exact resolve eq40 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq223
  have eq247 : ∀ X0 : G, (k X0 (σ (σ y))) = (σ (M.op (σ y) (τ X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq170 eq41
    | exact resolve eq41 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq261 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq230 eq14
    | exact resolve eq14 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq307 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq261 eq165
    | exact resolve eq165 eq261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq261
  have eq310 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq307
  have eq315 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq310 eq230
    | exact resolve eq230 eq310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310
  have eq320 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq315
  have eq372 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq320 eq172
    | exact resolve eq172 eq320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq320
  have eq378 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq372
  have eq384 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq378 eq13
    | (have j0 := eq13 X0 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq13 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq385 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq384 X0
       grind)
    | (have r₁ := eq384 X0
       have r₂ := eq230
       grind)
    | exact resolve eq384 eq230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq384
  have eq618 : ∀ X0 : G, (k (σ X0) (σ (σ y))) = (σ (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq247 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq247
    | exact resolve eq247 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq644 : ∀ X0 : G, (σ (M.op (σ y) X0)) = (σ (k X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq618 X0
       have i₂ := eq10 X0 sF3
       grind)
    | exact superpose eq10 eq618
    | exact resolve eq618 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq741 : (σ (M.op (σ x) (σ y))) = (σ (M.op (σ y) (σ x))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq199 eq644
    | exact resolve eq644 eq199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644
  have eq757 : (σ (M.op (σ x) (σ y))) = (σ (M.op (σ y) (σ x))) ∨ y = (M.op x y) := by grind
  clear eq741
  have eq768 : (σ (M.op (σ x) (σ y))) = (σ (M.op (σ x) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35 eq757
    | exact resolve eq757 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq769 : (σ (σ y)) = (σ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134 eq768
    | exact resolve eq768 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq783 : (σ (σ y)) = (σ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq769
  have eq793 : (σ (σ y)) = (σ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq783
    | exact resolve eq783 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783
  have eq795 : ∀ X0 : G, (k (σ X0) (σ (σ y))) = (σ (k X0 (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq793 eq10
    | exact resolve eq10 eq793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq814 : ∀ X0 : G, (σ (k X0 (σ y))) = (σ (k X0 (M.op (σ x) (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq795 X0
       have i₂ := eq10 X0 sF3
       grind)
    | exact superpose eq10 eq795
    | exact resolve eq795 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq1048 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = (τ (σ (k X0 (σ y)))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq814 eq16
    | exact resolve eq16 eq814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq1066 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1048 X0
       have i₂ := eq16 (k X0 sF3)
       grind)
    | exact superpose eq16 eq1048
    | exact resolve eq1048 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048
  have eq1073 : ∀ X0 : G, (k X0 (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1066 eq385
    | exact resolve eq385 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385 eq1066
  have eq1076 : ∀ X0 : G, (k X0 (σ y)) = (M.op (M.op (σ x) (σ y)) X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1073 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1073
  have eq1104 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1076 eq199
    | exact resolve eq199 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199 eq1076
  have eq1108 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1104
  have eq1118 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq134 eq1108
    | exact resolve eq1108 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134 eq1108
  have eq1130 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1118
  have eq1132 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq35 eq1130
    | exact resolve eq1130 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1130
  have eq1146 : (τ (σ y)) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1132 eq189
    | exact resolve eq189 eq1132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq1132
  have eq1157 : (τ (σ y)) = (k x y) ∨ y = (M.op x y) := by grind
  clear eq1146
  have eq1163 : y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq1157
    | exact resolve eq1157 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1157
  have eq1324 : ∀ X0 : G, (k X0 (τ (σ y))) = (τ (M.op (σ y) (σ X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq170 eq297
    | exact resolve eq297 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170 eq297
  have eq1336 : ∀ X0 : G, (k X0 y) = (τ (M.op (σ y) (σ X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq1324
    | exact resolve eq1324 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1324
  have eq2556 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1336 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1336
    | (have j0 := eq1336 y
       grind)
    | exact resolve eq1336 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1336
  have eq2599 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq166 eq2556
    | exact resolve eq2556 eq166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq166 eq2556
  have eq2615 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by grind
  clear eq2599
  have eq2619 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq2615
    | exact resolve eq2615 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2615
  have eq2664 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq67 y y
       have i₂ := eq2619
       grind)
    | exact superpose eq2619 eq67
    | (have j0 := eq67 y y
       grind)
    | exact resolve eq67 eq2619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2619
  have eq2665 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq2664
  have eq2671 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq2665
       grind)
    | exact superpose eq2665 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq2665
       grind)
    | exact resolve eq13 eq2665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2672 : ∀ X0 : G, (k X0 y) = (M.op y X0) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq2671 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2671
  have eq2823 : y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1163
       have i₂ := eq2672 x
       grind)
    | exact superpose eq2672 eq1163
    | exact resolve eq1163 eq2672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163 eq2672
  have eq2847 : y = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq2823
  have eq2862 : y = (M.op x (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2847
       have i₂ := eq34
       grind)
    | exact superpose eq34 eq2847
    | exact resolve eq2847 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2847
  have eq2866 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2862 eq38
    | exact resolve eq38 eq2862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2862
  have eq2875 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2665
       have i₂ := eq2866
       grind)
    | exact superpose eq2866 eq2665
    | exact resolve eq2665 eq2866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2665 eq2866
  have eq2889 : y = (M.op x y) := by grind
  clear eq2875
  have eq2891 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2889 eq20
    | exact resolve eq20 eq2889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2892 : y = (M.op y (M.op x y)) := by
    first
    | exact superpose eq2889 eq38
    | exact resolve eq38 eq2889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq2915 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq2892
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2892
    | exact resolve eq2892 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2892
  have eq2916 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2891
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2891
    | exact resolve eq2891 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2891
  have eq2917 : y = (M.op y y) := by
    first
    | exact superpose eq2889 eq2915
    | exact resolve eq2915 eq2889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2915
  have eq2988 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2916 eq26
    | exact resolve eq26 eq2916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq3056 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq2917
       grind)
    | exact superpose eq2917 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq2917
       grind)
    | exact resolve eq13 eq2917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3057 : ∀ X0 : G, (k X0 y) = (M.op y X0) := by
    intro X0
    first
    | (have j0 := eq3056 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3056
  have eq3205 : (k (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq53
       have i₂ := eq3057 x
       grind)
    | exact superpose eq3057 eq53
    | exact resolve eq53 eq3057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq3208 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq90
       have i₂ := eq3057 y
       grind)
    | exact superpose eq3057 eq90
    | exact resolve eq90 eq3057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq3057
  have eq3229 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq3208
       have i₂ := eq2917
       grind)
    | exact superpose eq2917 eq3208
    | exact resolve eq3208 eq2917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2917 eq3208
  have eq3230 : (k (σ x) (σ y)) = (σ (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq3205
       have i₂ := eq34
       grind)
    | exact superpose eq34 eq3205
    | exact resolve eq3205 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq3205
  have eq3241 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2916 eq3229
    | exact resolve eq3229 eq2916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3229
  have eq3242 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq2889 eq3230
    | exact resolve eq3230 eq2889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2889 eq3230
  have eq3247 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3241
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3241
    | exact resolve eq3241 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq3241
  have eq3248 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2916 eq3242
    | exact resolve eq3242 eq2916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3242
  have eq3252 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2916 eq3247
    | exact resolve eq3247 eq2916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2916 eq3247
  have eq3253 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq3248
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq3248
    | exact resolve eq3248 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3248
  have eq3257 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq3253
    | exact resolve eq3253 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq3253
  have eq3260 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3252 eq67
    | (have j0 := eq67 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq67 eq3252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq3252
  have eq3261 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq3260
  have eq3486 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq3261 eq13
    | (have j0 := eq13 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (σ (M.op x y))
       have r₂ := eq3261
       grind)
    | exact resolve eq13 eq3261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3487 : ∀ X0 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have j0 := eq3486 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3486
  have eq3704 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq3257 eq3487
    | exact resolve eq3487 eq3257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3257 eq3487
  have eq3739 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq3704 eq14
    | exact resolve eq14 eq3704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3704
  have eq3746 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq3261 eq3739
    | exact resolve eq3739 eq3261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3261 eq3739
  have eq3749 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2988 eq3746
    | exact resolve eq3746 eq2988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2988 eq3746
  have eq3750 : False := by grind
  exact eq3750

/-- `Equation335`: `x ◇ y = y ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_pyy_pxy_Equation335 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law335 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law335.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq27 : ∀ X0 X1 X2 : G, (σ (k X2 (k X0 (τ X1)))) = (k (σ X2) (k (σ X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X2 (k X0 (τ X1))
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq15
    | exact resolve eq15 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq64 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1)
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq71 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X1 X0) X1) (M.op (M.op X1 X0) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq65 (M.op X1 X0) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 X0 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq82 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op X1 X0) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq71 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq71
    | exact resolve eq71 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq94 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq74 X0
       grind)
    | exact superpose eq74 eq12
    | (have j0 := eq12 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq74 X0
       grind)
    | exact resolve eq12 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq95 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq94 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq490 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq490 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq493 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq491 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq491 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq491 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq510 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq493 (σ X0)
       grind)
    | exact superpose eq493 eq15
    | exact resolve eq15 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq514 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ X0) (σ X0))) = (σ (k X1 (k X0 (τ (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X0 (σ X0) X1
       have i₂ := eq493 (σ X0)
       grind)
    | exact superpose eq493 eq27
    | exact resolve eq27 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq525 : ∀ X0 X1 : G, (k (σ X1) (M.op (σ X0) (σ X0))) = (σ (k X1 (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq514 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq514
    | exact resolve eq514 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514
  have eq529 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq510 X0
       have i₂ := eq493 X0
       grind)
    | exact superpose eq493 eq510
    | exact resolve eq510 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq510
  have eq544 : ∀ X0 X1 : G, (σ (k X1 (M.op X0 X0))) = (k (σ X1) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq525 X0 X1
       have i₂ := eq493 X0
       grind)
    | exact superpose eq493 eq525
    | exact resolve eq525 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493 eq525
  have eq558 : ∀ X0 X1 : G, (σ (k X1 (M.op X0 X0))) = (M.op (σ X1) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq544 X0 X1
       have i₂ := eq95 (σ X0) (σ X1)
       grind)
    | exact superpose eq95 eq544
    | exact resolve eq544 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq568 : ∀ X0 X1 : G, (σ (k X1 (M.op X0 X0))) = (M.op (σ X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq558 X0 X1
       have i₂ := eq529 X0
       grind)
    | exact superpose eq529 eq558
    | exact resolve eq558 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq572 : ∀ X0 X1 : G, (σ (M.op X1 (M.op X0 X0))) = (M.op (σ X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq568 X0 X1
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq568
    | exact resolve eq568 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq568
  have eq587 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq529 X0
       grind)
    | exact superpose eq529 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq529 X0
       grind)
    | exact superpose eq529 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq595 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq587 X0 X1
       have j1 := eq592 X0 X1
       grind)
    | (have r₁ := eq587 X0 X1
       have r₂ := eq592 X0 X1
       grind)
    | exact resolve eq587 eq592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587 eq592
  have eq1644 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq595 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq595
    | exact resolve eq595 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1661 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq595 X1 (σ X0)
       grind)
    | exact superpose eq595 eq15
    | (have j1 := eq595 X1 (σ X0)
       grind)
    | exact resolve eq15 eq595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595
  have eq1711 : ∀ X0 X1 : G, (M.op X1 (τ X0)) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq1644 X1 (τ X0)
       grind)
    | exact superpose eq1644 eq18
    | (have j1 := eq1644 X1 (τ X0)
       grind)
    | exact resolve eq18 eq1644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1644
  have eq2220 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1711 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1711
    | exact resolve eq1711 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1711
  have eq2331 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2220 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2220
    | (have j0 := eq2220 X0 X1
       grind)
    | exact resolve eq2220 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2220
  have eq4795 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1661 x y
       grind)
    | exact superpose eq1661 eq16
    | (have j1 := eq1661 x y
       grind)
    | exact resolve eq16 eq1661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1661
  have eq4994 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq4795
       have i₂ := eq2331 x y
       grind)
    | exact superpose eq2331 eq4795
    | (have j1 := eq2331 (σ x) (σ y)
       grind)
    | (have r₁ := eq4795
       have r₂ := eq2331 x y
       grind)
    | exact resolve eq4795 eq2331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2331 eq4795
  have eq4995 : y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq4994
  have eq5000 : (M.op y y) = (M.op y (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq17 x y
       have i₂ := eq4995
       grind)
    | exact superpose eq4995 eq17
    | exact resolve eq17 eq4995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq5005 : y = (M.op (M.op x y) (M.op (M.op x y) y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq82 y x
       have i₂ := eq4995
       grind)
    | exact superpose eq4995 eq82
    | exact resolve eq82 eq4995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4995
  have eq5009 : y = (M.op y (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq5005
       have i₂ := eq9 y (M.op x y)
       grind)
    | exact superpose eq9 eq5005
    | exact resolve eq5005 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5005
  have eq5060 : y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq5009
       have i₂ := eq5000
       grind)
    | exact superpose eq5000 eq5009
    | exact resolve eq5009 eq5000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5000 eq5009
  have eq5074 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y y) := by grind
  clear eq5060
  have eq5084 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq9 (σ x) (σ y)
       have i₂ := eq5074
       grind)
    | exact superpose eq5074 eq9
    | exact resolve eq9 eq5074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5091 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq82 (σ y) (σ x)
       have i₂ := eq5074
       grind)
    | exact superpose eq5074 eq82
    | exact resolve eq82 eq5074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq5074
  have eq5096 : (σ y) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5091
       have i₂ := eq9 (σ y) (M.op (σ x) (σ y))
       grind)
    | exact superpose eq9 eq5091
    | exact resolve eq5091 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5091
  have eq5101 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5084
       have i₂ := eq529 y
       grind)
    | exact superpose eq529 eq5084
    | exact resolve eq5084 eq529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq529 eq5084
  have eq5134 : (σ y) = (M.op (σ y) (σ (M.op y y))) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5096
       have i₂ := eq5101
       grind)
    | exact superpose eq5101 eq5096
    | exact resolve eq5096 eq5101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5096 eq5101
  have eq5151 : (σ y) = (M.op (σ y) (σ (M.op y y))) ∨ y = (M.op y y) := by grind
  clear eq5134
  have eq5160 : (σ y) = (σ (M.op y (M.op y y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5151
       have i₂ := eq572 y y
       grind)
    | exact superpose eq572 eq5151
    | exact resolve eq5151 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5151
  have eq5162 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5160
       have i₂ := eq9 y y
       grind)
    | exact superpose eq9 eq5160
    | exact resolve eq5160 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5160
  have eq5176 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq5162
       grind)
    | exact superpose eq5162 eq10
    | exact resolve eq10 eq5162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5162
  have eq5239 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq5176
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5176
    | exact resolve eq5176 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5176
  have eq5240 : y = (M.op y y) := by grind
  clear eq5239
  have eq5261 : ∀ X0 : G, (M.op (σ X0) (σ y)) = (σ (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq572 y x
       have i₂ := eq5240
       grind)
    | exact superpose eq5240 eq572
    | exact resolve eq572 eq5240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq5240
  have eq6006 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5261 x
       grind)
    | exact superpose eq5261 eq16
    | (have r₁ := eq16
       have r₂ := eq5261 x
       grind)
    | exact resolve eq16 eq5261
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5261
  have eq6063 : False := by grind
  exact eq6063

/-- `Equation335`: `x ◇ y = y ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxy_pxx_pyx_Equation335 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law335 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law335.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq22
  have eq110 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 (M.op X0 X1))) = (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op X0 X1)
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq18
    | exact resolve eq18 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X1)
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq113 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq113
    | exact resolve eq113 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq117 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X0)) (M.op X0 X1)) = (M.op (M.op X0 X1) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq110 X0 X1
       have i₂ := eq9 X1 X0
       grind)
    | exact superpose eq9 eq110
    | exact resolve eq110 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq208 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X1 X0) X1) (M.op (M.op X1 X0) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq114 (M.op X1 X0) X1
       have i₂ := eq9 X0 X1
       grind)
    | exact superpose eq9 eq114
    | exact resolve eq114 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq114 X0 X0
       have i₂ := eq9 X0 X0
       grind)
    | exact superpose eq9 eq114
    | exact resolve eq114 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq231 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 (M.op X0 X1)) (M.op (M.op X1 X0) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq208 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq208
    | exact resolve eq208 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq341 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 X1) = X0 ∨ (k (M.op X0 X1) X0) = (M.op (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) X0
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 (M.op X0 X1) X0
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq358 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq359 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq2295 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq358 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq358
    | exact resolve eq358 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358
  have eq2347 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2295 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2295
    | (have j0 := eq2295 X0 X1
       grind)
    | exact resolve eq2295 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2295
  have eq2805 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq359 x y
       grind)
    | exact superpose eq359 eq16
    | (have j1 := eq359 x y
       grind)
    | exact resolve eq16 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq12338 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq2805
       have i₂ := eq2347 x y
       grind)
    | exact superpose eq2347 eq2805
    | (have j1 := eq2347 (σ x) (σ y)
       grind)
    | (have r₁ := eq2805
       have r₂ := eq2347 x y
       grind)
    | (have r₁ := eq2805
       have r₂ := eq2347 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2805
       have r₂ := eq2347 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2805 eq2347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2347
  have eq12339 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq12338
  have eq18452 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq12339
       grind)
    | exact superpose eq12339 eq16
    | exact resolve eq16 eq12339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12339
  have eq18453 : y = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq18452
       have r₂ := eq23 x
       grind)
    | exact resolve eq18452 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18452
  have eq18454 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq9 x y
       have i₂ := eq18453
       grind)
    | exact superpose eq18453 eq9
    | exact resolve eq9 eq18453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18463 : y = (M.op (M.op x y) (M.op (M.op x y) y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq231 y x
       have i₂ := eq18453
       grind)
    | exact superpose eq18453 eq231
    | exact resolve eq231 eq18453
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18453
  have eq18467 : y = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq18463
       have i₂ := eq9 y (M.op x y)
       grind)
    | exact superpose eq9 eq18463
    | exact resolve eq18463 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18463
  have eq18476 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq18454
       grind)
    | exact superpose eq18454 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq18454
       grind)
    | exact resolve eq13 eq18454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18454
  have eq18487 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq18476
  have eq18488 : (σ x) = (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq18487
  have eq18498 : (σ (k y x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq18488
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq18488
    | exact resolve eq18488 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18488
  have eq18502 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq18498
       have i₂ := eq23 y
       grind)
    | exact superpose eq23 eq18498
    | exact resolve eq18498 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18498
  have eq23382 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq18502
       grind)
    | exact superpose eq18502 eq10
    | exact resolve eq10 eq18502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18502
  have eq23440 : x = y ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq23382
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq23382
    | exact resolve eq23382 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23382
  have eq23442 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23440
       grind)
    | exact superpose eq23440 eq16
    | exact resolve eq16 eq23440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23440
  have eq23443 : (σ (k y x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq23442
       have r₂ := eq23 x
       grind)
    | exact resolve eq23442 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23442
  have eq23451 : (k y x) = (τ (σ (M.op y y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq23443
       grind)
    | exact superpose eq23443 eq10
    | exact resolve eq10 eq23443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23443
  have eq23509 : (k y x) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq23451
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq23451
    | exact resolve eq23451 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23451
  have eq23513 : (M.op x y) = (M.op y y) ∨ y = (M.op y x) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq23509
       grind)
    | exact superpose eq23509 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq23509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23509
  have eq23534 : x = y ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq23513
  have eq23536 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23534
       grind)
    | exact superpose eq23534 eq16
    | exact resolve eq16 eq23534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23534
  have eq23537 : y = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq23536
       have r₂ := eq23 x
       grind)
    | exact resolve eq23536 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23536
  have eq23538 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq9 x y
       have i₂ := eq23537
       grind)
    | exact superpose eq23537 eq9
    | exact resolve eq9 eq23537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23537
  have eq23553 : (M.op x y) = (M.op y y) := by grind
  clear eq23538
  have eq23578 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq217 y
       have i₂ := eq23553
       grind)
    | exact superpose eq23553 eq217
    | exact resolve eq217 eq23553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217
  have eq23684 : (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq9 y y
       have i₂ := eq23553
       grind)
    | exact superpose eq23553 eq9
    | exact resolve eq9 eq23553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23710 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18467
       have i₂ := eq23684
       grind)
    | exact superpose eq23684 eq18467
    | exact resolve eq18467 eq23684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18467
  have eq23714 : (M.op (M.op y x) (M.op x y)) = (M.op (M.op x y) (M.op y x)) := by
    first
    | (have i₁ := eq117 y x
       have i₂ := eq23684
       grind)
    | exact superpose eq23684 eq117
    | exact resolve eq117 eq23684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23715 : (M.op x y) = (M.op (M.op y x) (M.op x y)) := by
    first
    | (have i₁ := eq114 y x
       have i₂ := eq23684
       grind)
    | exact superpose eq23684 eq114
    | exact resolve eq114 eq23684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq23684
  have eq23741 : (M.op x y) = (M.op (M.op x y) (M.op y x)) := by
    first
    | (have i₁ := eq23714
       have i₂ := eq23715
       grind)
    | exact superpose eq23715 eq23714
    | exact resolve eq23714 eq23715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23714 eq23715
  have eq23949 : (M.op y x) = (M.op (M.op x (M.op y x)) (M.op x y)) := by
    first
    | (have i₁ := eq231 y x
       have i₂ := eq23741
       grind)
    | exact superpose eq23741 eq231
    | exact resolve eq231 eq23741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231
  have eq23976 : (M.op y x) = (M.op (M.op x y) (M.op y x)) := by
    first
    | (have i₁ := eq23949
       have i₂ := eq117 x y
       grind)
    | exact superpose eq117 eq23949
    | exact resolve eq23949 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq23949
  have eq23984 : (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq23976
       have i₂ := eq23741
       grind)
    | exact superpose eq23741 eq23976
    | exact resolve eq23976 eq23741
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23741 eq23976
  have eq24005 : (M.op x y) ≠ (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ (M.op (M.op x y) (M.op x y)) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq341 x y
       have i₂ := eq23984
       grind)
    | exact superpose eq23984 eq341
    | (have j0 := eq341 x y
       grind)
    | exact resolve eq341 eq23984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341
  have eq24006 : (M.op x y) ≠ (M.op y x) ∨ x = (M.op x y) ∨ (M.op (M.op x y) (M.op x y)) = (k (M.op x y) x) := by
    first
    | (have i₁ := eq24005
       have i₂ := eq9 y x
       grind)
    | exact superpose eq9 eq24005
    | exact resolve eq24005 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24005
  have eq24012 : x = (M.op x y) ∨ (M.op (M.op x y) (M.op x y)) = (k (M.op x y) x) := by
    first
    | (have r₁ := eq24006
       have r₂ := eq23984
       grind)
    | exact resolve eq24006 eq23984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23984 eq24006
  have eq24016 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24012
       have i₂ := eq23578
       grind)
    | exact superpose eq23578 eq24012
    | exact resolve eq24012 eq23578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23578 eq24012
  have eq28745 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9 (σ x) (σ y)
       have i₂ := eq23710
       grind)
    | exact superpose eq23710 eq9
    | exact resolve eq9 eq23710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23710
  have eq28771 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28745
       have i₂ := eq23 y
       grind)
    | exact superpose eq23 eq28745
    | exact resolve eq28745 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28745
  have eq28776 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28771
       have i₂ := eq23553
       grind)
    | exact superpose eq23553 eq28771
    | exact resolve eq28771 eq23553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28771
  have eq28779 : (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq28776
       have r₂ := eq16
       grind)
    | exact resolve eq28776 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28776
  have eq28780 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28779
       grind)
    | exact superpose eq28779 eq16
    | exact resolve eq16 eq28779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28790 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23 y
       have i₂ := eq28779
       grind)
    | exact superpose eq28779 eq23
    | exact resolve eq23 eq28779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28779
  have eq28852 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28790
       have i₂ := eq23553
       grind)
    | exact superpose eq23553 eq28790
    | exact resolve eq28790 eq23553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28790
  have eq28856 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28780
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq28780
    | exact resolve eq28780 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28780
  have eq28857 : (σ (M.op x y)) = (σ (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq28852
       have i₂ := eq23 x
       grind)
    | exact superpose eq23 eq28852
    | exact resolve eq28852 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28852
  have eq28858 : y = (M.op x y) := by
    first
    | (have r₁ := eq28857
       have r₂ := eq28856
       grind)
    | exact resolve eq28857 eq28856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28856 eq28857
  have eq28885 : y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq24016
       have i₂ := eq28858
       grind)
    | exact superpose eq28858 eq24016
    | exact resolve eq24016 eq28858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24016
  have eq29149 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2805
       have i₂ := eq28885
       grind)
    | exact superpose eq28885 eq2805
    | exact resolve eq2805 eq28885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2805 eq28885
  have eq29195 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq29149
       have i₂ := eq28858
       grind)
    | exact superpose eq28858 eq29149
    | exact resolve eq29149 eq28858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28858 eq29149
  have eq29196 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq29195
  have eq29620 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq9 (σ x) (σ y)
       have i₂ := eq29196
       grind)
    | exact superpose eq29196 eq9
    | exact resolve eq9 eq29196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29196
  have eq29646 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq29620
       have i₂ := eq23 y
       grind)
    | exact superpose eq23 eq29620
    | exact resolve eq29620 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29620
  have eq29651 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq29646
       have i₂ := eq23553
       grind)
    | exact superpose eq23553 eq29646
    | exact resolve eq29646 eq23553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23553 eq29646
  have eq29655 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq29651
       have r₂ := eq16
       grind)
    | exact resolve eq29651 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29651
  have eq29664 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq29655
       grind)
    | exact superpose eq29655 eq10
    | exact resolve eq10 eq29655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29655
  have eq29732 : x = y ∨ x = y := by
    first
    | (have i₁ := eq29664
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29664
    | exact resolve eq29664 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29664
  have eq29733 : x = y := by grind
  clear eq29732
  have eq29750 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29733
       grind)
    | exact superpose eq29733 eq16
    | exact resolve eq16 eq29733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29733
  have eq29809 : False := by grind
  exact eq29809

/-- `Equation335`: `x ◇ y = y ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_x_pxy_pxx_pyx_Equation335 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law335 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law335.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq20 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq23 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq24 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq23
  have eq47 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9 (σ X0) (σ X0)
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq345 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq347 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq350 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq345 X0 X1
       have i₂ := eq24 X0
       grind)
    | exact superpose eq24 eq345
    | (have j0 := eq345 X0 X1
       grind)
    | exact resolve eq345 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq2352 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq347 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq347
    | exact resolve eq347 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq2405 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2352 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2352
    | (have j0 := eq2352 X0 X1
       grind)
    | exact resolve eq2352 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2352
  have eq2730 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq350 x y
       grind)
    | exact superpose eq350 eq16
    | (have j1 := eq350 x y
       grind)
    | exact resolve eq16 eq350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq350
  have eq7094 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq2730
       have i₂ := eq2405 y x
       grind)
    | exact superpose eq2405 eq2730
    | (have j1 := eq2405 y x
       grind)
    | (have r₁ := eq2730
       have r₂ := eq2405 y x
       grind)
    | (have r₁ := eq2730
       have r₂ := eq2405 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2730
       have r₂ := eq2405 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2730 eq2405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2405 eq2730
  have eq7095 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by grind
  clear eq7094
  have eq9856 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7095
       grind)
    | exact superpose eq7095 eq16
    | exact resolve eq16 eq7095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7095
  have eq9857 : (σ x) = (σ y) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq9856
       have r₂ := eq24 x
       grind)
    | exact resolve eq9856 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9856
  have eq9859 : y = (τ (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq9857
       grind)
    | exact superpose eq9857 eq10
    | exact resolve eq10 eq9857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9857
  have eq9911 : x = y ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq9859
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq9859
    | exact resolve eq9859 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9859
  have eq9913 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x x) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9911
       grind)
    | exact superpose eq9911 eq16
    | exact resolve eq16 eq9911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9911
  have eq9914 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq9913
       have r₂ := eq24 x
       grind)
    | exact resolve eq9913 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq9913
  have eq9923 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq9914
       grind)
    | exact superpose eq9914 eq10
    | exact resolve eq10 eq9914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9914
  have eq9984 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq9923
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq9923
    | exact resolve eq9923 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9923
  have eq9985 : y = (M.op x x) := by grind
  clear eq9984
  have eq9989 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq9985
       grind)
    | exact superpose eq9985 eq47
    | exact resolve eq47 eq9985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq10041 : y = (M.op x y) := by
    first
    | (have i₁ := eq9 x x
       have i₂ := eq9985
       grind)
    | exact superpose eq9985 eq9
    | exact resolve eq9 eq9985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9985
  have eq10214 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq9989
       grind)
    | exact superpose eq9989 eq16
    | exact resolve eq16 eq9989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9989
  have eq10236 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq10214
       have i₂ := eq10041
       grind)
    | exact superpose eq10041 eq10214
    | exact resolve eq10214 eq10041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10041 eq10214
  have eq10237 : False := by grind
  exact eq10237

/-- `Equation3352`: `x ◇ y = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_pyy_pyx_pyy_pyx_Equation3352 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3352 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3352.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq83 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq272 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq83 X0 X1
       grind)
    | exact superpose eq83 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq83 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq83 X1 X1
       grind)
    | exact resolve eq13 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq274 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq83 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq275 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq272 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq276 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq275 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq279 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq276 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq276
    | (have j0 := eq276 X0 X1
       grind)
    | exact resolve eq276 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq276
  have eq283 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq279 X0 X1
       have j1 := eq274 X0 X1
       grind)
    | (have r₁ := eq279 X0 X1
       have r₂ := eq274 X0 X1
       grind)
    | (have r₁ := eq279 X0 (k X1 X0)
       have r₂ := eq274 X0 X1
       grind)
    | (have r₁ := eq279 X0 X0
       have r₂ := eq274 X0 X0
       grind)
    | exact resolve eq279 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274 eq279
  have eq517 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq283 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq283
    | exact resolve eq283 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq531 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq283 x y
       grind)
    | exact superpose eq283 eq16
    | (have j1 := eq283 x y
       grind)
    | exact resolve eq16 eq283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283
  have eq546 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq517 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq517
    | (have j0 := eq517 X0 X1
       grind)
    | exact resolve eq517 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq517
  have eq547 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq546
    | exact resolve eq546 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546
  have eq606 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq547 (τ X1) X0
       grind)
    | exact superpose eq547 eq18
    | (have j1 := eq547 (τ X1) X0
       grind)
    | exact resolve eq18 eq547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq547
  have eq826 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq606 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq606
    | exact resolve eq606 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq873 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq826 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq826
    | (have j0 := eq826 X0 X1
       grind)
    | exact resolve eq826 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq972 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq531
       have i₂ := eq873 y x
       grind)
    | exact superpose eq873 eq531
    | (have j1 := eq873 (σ y) (σ x)
       grind)
    | (have r₁ := eq531
       have r₂ := eq873 y x
       grind)
    | exact resolve eq531 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq973 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq972
  have eq980 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq973
  have eq989 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq531
       have i₂ := eq980
       grind)
    | exact superpose eq980 eq531
    | exact resolve eq531 eq980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq531 eq980
  have eq990 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq989
  have eq991 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq990
  have eq1004 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq991
  have eq1011 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1004
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1004
    | exact resolve eq1004 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004
  have eq1059 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1011
       grind)
    | exact superpose eq1011 eq16
    | exact resolve eq16 eq1011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1011
  have eq1065 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1059
       have i₂ := eq873 y x
       grind)
    | exact superpose eq873 eq1059
    | (have j1 := eq873 y x
       grind)
    | (have r₁ := eq1059
       have r₂ := eq873 y x
       grind)
    | exact resolve eq1059 eq873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq873
  have eq1066 : y = (M.op x x) := by grind
  clear eq1065
  have eq1094 : (M.op x y) = (k y x) := by grind
  clear eq1066
  have eq1103 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1059
       have i₂ := eq1094
       grind)
    | exact superpose eq1094 eq1059
    | exact resolve eq1059 eq1094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059 eq1094
  have eq1106 : False := by grind
  exact eq1106

/-- `Equation3352`: `x ◇ y = y ◇ (y ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyx_pyx_pxx_pyx_Equation3352 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3352 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3352.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq27 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq39 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq41 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X0 X2) ∨ (M.op X0 X2) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq27 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq42 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq99 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq42 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq228 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq229 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq228 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq234 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq229 X0 X1
       have j1 := eq99 X0 X1
       grind)
    | (have r₁ := eq229 X0 X1
       have r₂ := eq99 X0 X1
       grind)
    | (have r₁ := eq229 X0 X0
       have r₂ := eq99 X0 X0
       grind)
    | exact resolve eq229 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq229
  have eq372 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq234 (σ X1) (σ X0)
       grind)
    | exact superpose eq234 eq15
    | exact resolve eq15 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq379 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq372 X0 X1
       have i₂ := eq234 X1 X0
       grind)
    | exact superpose eq234 eq372
    | exact resolve eq372 eq234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234 eq372
  have eq382 : False := by grind
  exact eq382

/-- `Equation3461`: `x ◇ x = x ◇ ((y ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxy_y_pxy_y_pxy_Equation3461 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3461 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3461.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq22
    | exact resolve eq22 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq265 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265
  have eq268 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq266 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq266 X0
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq266 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266
  have eq279 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq268 (σ X0)
       grind)
    | exact superpose eq268 eq15
    | exact resolve eq15 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq268 (τ X0)
       grind)
    | exact superpose eq268 eq31
    | exact resolve eq31 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq292 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq285 X0
       have i₂ := eq268 X0
       grind)
    | exact superpose eq268 eq285
    | exact resolve eq285 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq298 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq279 X0
       have i₂ := eq268 X0
       grind)
    | exact superpose eq268 eq279
    | exact resolve eq279 eq268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268 eq279
  have eq343 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) X1
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq14
    | (have j0 := eq14 (σ X0) X1
       grind)
    | exact resolve eq14 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq298 X0
       grind)
    | exact superpose eq298 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298
  have eq345 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (k (σ X0) X1) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq343 X0 X1
       have j1 := eq344 X0 X1
       grind)
    | (have r₁ := eq343 X0 X1
       have r₂ := eq344 X0 X1
       grind)
    | exact resolve eq343 eq344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343 eq344
  have eq358 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op (τ X0) X1) = X1 ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ X0) X1
       have i₂ := eq292 X0
       grind)
    | exact superpose eq292 eq14
    | (have j0 := eq14 (τ X0) X1
       grind)
    | exact resolve eq14 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq359 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k (τ X0) X1) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq292 X0
       grind)
    | exact superpose eq292 eq12
    | (have j0 := eq12 (τ X0) X1
       grind)
    | exact resolve eq12 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq360 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq358 X0 X1
       have j1 := eq359 X0 X1
       grind)
    | (have r₁ := eq358 X0 X1
       have r₂ := eq359 X0 X1
       grind)
    | exact resolve eq358 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq358 eq359
  have eq379 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq345 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq345
    | exact resolve eq345 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq345 x (σ y)
       grind)
    | exact superpose eq345 eq16
    | (have j1 := eq345 x (σ y)
       grind)
    | exact resolve eq16 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq389 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) X0) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) X0
       have i₂ := eq345 X1 X0
       grind)
    | exact superpose eq345 eq13
    | (have j0 := eq13 (σ X1) X0
       have j1 := eq345 X1 (σ X1)
       grind)
    | (have r₁ := eq13 (σ X0) X1
       have r₂ := eq345 X0 X1
       grind)
    | exact resolve eq13 eq345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq345
  have eq395 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X1) (σ X1)) ∨ (k (σ X1) X0) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq389 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq397 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (k (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq395 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq395 X0 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq395 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq399 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq385
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq385
    | exact resolve eq385 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq409 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq379 X1 X0
       grind)
    | exact superpose eq379 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq379 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq379 X0 X1
       grind)
    | exact resolve eq13 eq379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq420 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq409 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq424 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq420 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq420 X0 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq420 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq449 : ∀ X0 X1 : G, (k (τ X0) X1) = X1 ∨ (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq424 X1 (τ X0)
       grind)
    | exact superpose eq424 eq17
    | (have j1 := eq424 X1 (τ X0)
       grind)
    | exact resolve eq17 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq455 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq424 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (τ X1)
       have i₂ := eq449 X1 (τ X0)
       grind)
    | exact superpose eq449 eq18
    | (have j1 := eq449 X1 (τ X0)
       grind)
    | exact resolve eq18 eq449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq449
  have eq693 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq686 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq686
    | (have j0 := eq686 X0 X1
       grind)
    | exact resolve eq686 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq704 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 (σ (τ X0))) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq693 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq693
    | (have j0 := eq693 X0 X1
       grind)
    | exact resolve eq693 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq705 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X1 X0) = (σ (M.op (τ X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq704 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq704
    | (have j0 := eq704 X0 X1
       grind)
    | exact resolve eq704 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq758 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq705 X0 X1
       have i₂ := eq424 X0 X1
       grind)
    | exact superpose eq424 eq705
    | (have j0 := eq705 X1 X0
       have j1 := eq424 X1 X0
       grind)
    | exact resolve eq705 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq762 : ∀ X0 X1 : G, (M.op (σ X0) X1) = X1 ∨ (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq705 X0 (σ X1)
       have i₂ := eq397 X0 X1
       grind)
    | exact superpose eq397 eq705
    | (have j0 := eq705 X1 (σ X0)
       have j1 := eq397 X1 X0
       grind)
    | exact resolve eq705 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq705
  have eq817 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) (τ X1))) ∨ (k (σ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq762 X0 X1
       have j1 := eq455 (σ X0) X1
       grind)
    | (have r₁ := eq762 X0 X1
       have r₂ := eq455 (σ X0) X1
       grind)
    | exact resolve eq762 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq821 : ∀ X0 X1 : G, (k X0 X1) = X1 ∨ (M.op X0 X1) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq758 X0 X1
       have j1 := eq455 X0 X1
       grind)
    | (have r₁ := eq758 X0 X1
       have r₂ := eq455 X0 X1
       grind)
    | exact resolve eq758 eq455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455 eq758
  have eq838 : ∀ X0 X1 : G, (k (σ X0) X1) = X1 ∨ (M.op (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq817 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq817
    | (have j0 := eq817 X0 X1
       grind)
    | exact resolve eq817 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq862 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ X1) X0) ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 X1 X0
       have i₂ := eq821 X1 (σ X0)
       grind)
    | exact superpose eq821 eq22
    | (have j1 := eq821 X1 (σ X0)
       grind)
    | exact resolve eq22 eq821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq821
  have eq898 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq862 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq862
    | (have j0 := eq862 X0 X1
       grind)
    | exact resolve eq862 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq917 : ∀ X0 X1 : G, (k (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq898 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq898
    | (have j0 := eq898 X0 X1
       grind)
    | exact resolve eq898 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq898
  have eq1115 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (σ X1)) X0) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (σ X1) X0
       have i₂ := eq838 X1 (σ X0)
       grind)
    | exact superpose eq838 eq22
    | (have j1 := eq838 X1 (σ X0)
       grind)
    | exact resolve eq22 eq838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq838
  have eq1122 : ∀ X0 X1 : G, (τ (σ X0)) = (k X1 X0) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1115 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1115
    | (have j0 := eq1115 X0 X1
       grind)
    | exact resolve eq1115 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1115
  have eq1139 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1122 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1122
    | (have j0 := eq1122 X0 X1
       grind)
    | exact resolve eq1122 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq1148 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1139 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1139
    | (have j0 := eq1139 X0 X1
       grind)
    | exact resolve eq1139 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1139
  have eq1165 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1148 y x
       grind)
    | exact superpose eq1148 eq16
    | (have j1 := eq1148 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq1148 y x
       grind)
    | exact resolve eq16 eq1148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1148
  have eq1183 : y = (k x y) := by grind
  clear eq1165
  have eq1473 : ∀ X0 X1 : G, (M.op (τ X1) X0) = X0 ∨ (M.op (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq360 X1 X0
       have i₂ := eq917 X0 X1
       grind)
    | exact superpose eq917 eq360
    | (have j0 := eq360 X1 X0
       have j1 := eq917 X0 X1
       grind)
    | exact resolve eq360 eq917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360 eq917
  have eq1486 : ∀ X0 X1 : G, (M.op (τ X1) X0) = X0 ∨ (M.op X1 (σ X0)) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1473 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq1613 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1486 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1486
    | exact resolve eq1486 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1486
  have eq1709 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1613 x y
       grind)
    | exact superpose eq1613 eq16
    | (have j1 := eq1613 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1613 x y
       grind)
    | exact resolve eq16 eq1613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1613
  have eq1728 : y = (M.op x y) := by grind
  clear eq1709
  have eq1771 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq399
       have i₂ := eq1728
       grind)
    | exact superpose eq1728 eq399
    | exact resolve eq399 eq1728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq1776 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq1771
  have eq1779 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1776
       have i₂ := eq1183
       grind)
    | exact superpose eq1183 eq1776
    | exact resolve eq1776 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183 eq1776
  have eq1784 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1779
       grind)
    | exact superpose eq1779 eq16
    | exact resolve eq16 eq1779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779
  have eq1800 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq1784
       have i₂ := eq1728
       grind)
    | exact superpose eq1728 eq1784
    | exact resolve eq1784 eq1728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1728 eq1784
  have eq1801 : False := by grind
  exact eq1801
