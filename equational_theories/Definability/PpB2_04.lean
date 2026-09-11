import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pyy_pxy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
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
  have eq31 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq21
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
  have eq47 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq91 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq92 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq91
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq91
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq96
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq96
    | exact resolve eq96 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq103 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq21 eq102
    | exact resolve eq102 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq109 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq38 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq38
    | (have j0 := eq38 x
       grind)
    | exact resolve eq38 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq38 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq38
    | (have j0 := eq38 y
       grind)
    | exact resolve eq38 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq16
    | exact resolve eq16 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq129 : (k (σ (M.op x y)) (σ x)) = (σ (M.op x (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq109
       have i₂ := eq11 sF0 x
       grind)
    | exact superpose eq11 eq109
    | (have j1 := eq11 (M.op x y) x
       grind)
    | exact resolve eq109 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq109 eq16
    | exact resolve eq16 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq110 eq16
    | exact resolve eq16 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq160 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq111 eq16
    | exact resolve eq16 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq245 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq52 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq52
    | (have j0 := eq52 y x
       grind)
    | exact resolve eq52 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) X1 X2
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 y) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq245 eq14
    | exact resolve eq14 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq412 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 (M.op X0 X0) X0 X1 X2
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq49 y x X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq49
    | (have j0 := eq49 y x X0 X1
       grind)
    | exact resolve eq49 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq49 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq49
    | exact resolve eq49 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op X2 (M.op X1 (M.op x y))) (M.op (M.op X0 x) (M.op X0 x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq47 eq49
    | exact resolve eq49 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq49
  have eq566 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq61 X0 X0
       grind)
    | exact superpose eq61 eq50
    | (have j1 := eq61 X0 X0
       grind)
    | exact resolve eq50 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq61 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq576 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq575 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575
  have eq580 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq566 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq3381 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq425 X0 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq425
    | exact resolve eq425 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq3407 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq3381 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3381
    | (have j0 := eq3381 y x
       grind)
    | exact resolve eq3381 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3591 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq430 x X1 X0
       have i₂ := eq52 x x
       grind)
    | exact superpose eq52 eq430
    | exact resolve eq430 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq3654 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3591 sF0 sF0
       have i₂ := eq50 sF0
       grind)
    | exact superpose eq50 eq3591
    | exact resolve eq3591 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3591
  have eq3678 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 (M.op x x)) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq3654 eq14
    | exact resolve eq14 eq3654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3823 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq421 (M.op y X0) X0
       have i₂ := eq52 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq52 eq421
    | exact resolve eq421 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq4014 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq428 X0 X0 X2 X3 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq428
    | exact resolve eq428 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq4031 : (M.op x y) = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq3678 x
       have i₂ := eq50 x
       grind)
    | exact superpose eq50 eq3678
    | exact resolve eq3678 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3678
  have eq6497 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq412 X0 X1 (M.op X0 X0)
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq412
    | exact resolve eq412 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412
  have eq13740 : ∀ X0 : G, (M.op y y) = (M.op (M.op X0 (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq258 eq250
    | exact resolve eq250 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq13850 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op X0 (M.op y y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq13740 eq250
    | exact resolve eq250 eq13740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq13740
  have eq14113 : (M.op (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq13850 y
       have i₂ := eq50 y
       grind)
    | exact superpose eq50 eq13850
    | exact resolve eq13850 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13850
  have eq18366 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4014 X0 (M.op X0 X1) (M.op X0 X1) X1
       have i₂ := eq50 (M.op X0 X1)
       grind)
    | exact superpose eq50 eq4014
    | exact resolve eq4014 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4014
  have eq23653 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23654 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq23653
    | exact resolve eq23653 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23653
  have eq23665 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq23654
       have r₂ := eq28
       grind)
    | exact resolve eq23654 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23654
  have eq23681 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23665 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq23665
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq23665
       grind)
    | exact resolve eq12 eq23665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23665
  have eq23697 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq23681
  have eq23698 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq23697
  have eq23708 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq23698 eq103
    | exact resolve eq103 eq23698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23698
  have eq23721 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq23708
  have eq23743 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq23721
  have eq24454 : (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq23743 eq103
    | exact resolve eq103 eq23743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq23743
  have eq24466 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by grind
  clear eq24454
  have eq24778 : (M.op x x) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq3381 x y
       have i₂ := eq24466
       grind)
    | exact superpose eq24466 eq3381
    | exact resolve eq3381 eq24466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26312 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq24466
       have i₂ := eq24778
       grind)
    | exact superpose eq24778 eq24466
    | exact resolve eq24466 eq24778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24466 eq24778
  have eq26349 : y = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq26312
  have eq26365 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq26349
       grind)
    | exact superpose eq26349 eq50
    | exact resolve eq50 eq26349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq26366 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq52 x X0
       have i₂ := eq26349
       grind)
    | exact superpose eq26349 eq52
    | exact resolve eq52 eq26349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26388 : y = (M.op x (M.op y y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq6497 x x
       have i₂ := eq26349
       grind)
    | exact superpose eq26349 eq6497
    | exact resolve eq6497 eq26349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26394 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26365
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq26365
    | exact resolve eq26365 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26365
  have eq26397 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26394 eq27
    | exact resolve eq27 eq26394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26398 : y = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26394 eq30
    | exact resolve eq30 eq26394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26399 : ∀ X0 : G, (σ (k y X0)) = (k (σ (M.op x y)) (σ X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26394 eq37
    | exact resolve eq37 eq26394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq26411 : (k y y) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26394 eq120
    | exact resolve eq120 eq26394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq26417 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26394 eq152
    | exact resolve eq152 eq26394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq26564 : (k (M.op x y) y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq160 eq26417
    | exact resolve eq26417 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26417
  have eq26570 : (k y y) = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq160 eq26411
    | exact resolve eq26411 eq160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq26411
  have eq26580 : ∀ X0 : G, (σ (k y X0)) = (σ (k (M.op x y) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq38 eq26399
    | exact resolve eq26399 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq26399
  have eq26581 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq26398
    | exact resolve eq26398 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26398
  have eq26657 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26581 eq3654
    | exact resolve eq3654 eq26581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26659 : y = (M.op x (M.op y y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26581 eq4031
    | exact resolve eq4031 eq26581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4031
  have eq26702 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq27599 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq3381 y (M.op x x)
       have i₂ := eq26366 x
       grind)
    | exact superpose eq26366 eq3381
    | exact resolve eq3381 eq26366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3381 eq26366
  have eq27612 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq27599
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq27599
    | exact resolve eq27599 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27599
  have eq27952 : y = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq26388
       have i₂ := eq27612
       grind)
    | exact superpose eq27612 eq26388
    | exact resolve eq26388 eq27612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26388 eq27612
  have eq27990 : y = (M.op x (M.op x y)) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq27952
  have eq28406 : (k y y) = (k (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26570 eq26564
    | exact resolve eq26564 eq26570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26564 eq26570
  have eq28424 : (k y y) = (k (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq28406
  have eq29149 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3823 x
       have i₂ := eq26657
       grind)
    | exact superpose eq26657 eq3823
    | exact resolve eq3823 eq26657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3823 eq26657
  have eq29184 : x = (M.op (M.op x y) (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq29149
       have i₂ := eq52 x x
       grind)
    | exact superpose eq52 eq29149
    | exact resolve eq29149 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq29149
  have eq31179 : (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29184 eq18366
    | exact resolve eq18366 eq29184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29184
  have eq31181 : (M.op x (M.op x y)) = (M.op y (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14113 eq31179
    | exact resolve eq31179 eq14113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14113 eq31179
  have eq31271 : (M.op x y) = (M.op y y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26581 eq31181
    | exact resolve eq31181 eq26581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31181
  have eq31339 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq31271
       have r₂ := eq26702
       grind)
    | exact resolve eq31271 eq26702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26702 eq31271
  have eq31341 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31339
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq31339
    | exact resolve eq31339 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31339
  have eq31351 : y = (M.op x (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26659
       have i₂ := eq31341
       grind)
    | exact superpose eq31341 eq26659
    | exact resolve eq26659 eq31341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26659
  have eq31364 : (M.op x y) = (k (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq31341
  have eq31397 : y = (M.op x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq31351
  have eq31437 : (M.op x y) = (k y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31364 eq28424
    | exact resolve eq28424 eq31364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28424 eq31364
  have eq31443 : (M.op x y) = (k y y) ∨ x = (M.op x y) := by grind
  clear eq31437
  have eq32032 : (σ y) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq576 y
       have i₂ := eq31443
       grind)
    | exact superpose eq31443 eq576
    | (have j0 := eq576 y
       grind)
    | exact resolve eq576 eq31443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576 eq31443
  have eq32059 : (σ y) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq32032
    | exact resolve eq32032 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32032
  have eq32075 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32059
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32059
    | exact resolve eq32059 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32059
  have eq32082 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq32075
       have r₂ := eq26394
       grind)
    | exact resolve eq32075 eq26394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32075
  have eq32083 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq32082
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq32082
    | exact resolve eq32082 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32082
  have eq33118 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26394 eq32083
    | exact resolve eq32083 eq26394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32083
  have eq33170 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq33118
  have eq33593 : (M.op x y) = (M.op x x) ∨ (k (σ (M.op x y)) (σ x)) = (σ (M.op x (M.op x y))) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq3654 eq129
    | exact resolve eq129 eq3654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq3654
  have eq33594 : (k (σ (M.op x y)) (σ x)) = (σ (M.op x (M.op x y))) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq33593
  have eq33596 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31397 eq33594
    | exact resolve eq33594 eq31397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31397
  have eq33597 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27990 eq33594
    | exact resolve eq33594 eq27990
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27990 eq33594
  have eq33673 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq33597
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33597
    | exact resolve eq33597 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33597
  have eq33674 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq33596
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33596
    | exact resolve eq33596 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33596
  have eq193436 : (τ (σ y)) = (k (M.op x y) x) ∨ (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq33673 eq135
    | exact resolve eq135 eq33673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33673
  have eq193459 : (M.op x y) = (M.op x x) ∨ y = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq30 eq193436
    | exact resolve eq193436 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193436
  have eq195352 : y = (M.op x y) ∨ (σ (M.op x y)) = (σ y) ∨ y = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq26349
       have i₂ := eq193459
       grind)
    | exact superpose eq193459 eq26349
    | exact resolve eq26349 eq193459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26349
  have eq195399 : (M.op x y) = (k (M.op x y) x) ∨ y = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq193459
  have eq195467 : y = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq195352
  have eq197739 : y ≠ (M.op x y) ∨ y = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq195399
  have eq197742 : y = (k (M.op x y) x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq197739
       have r₂ := eq195467
       grind)
    | exact resolve eq197739 eq195467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195467 eq197739
  have eq197790 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq197742 eq109
    | exact resolve eq109 eq197742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq197836 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq197790
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq197790
    | exact resolve eq197790 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197790
  have eq200242 : (τ (σ y)) = (k (M.op x y) x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33674 eq135
    | exact resolve eq135 eq33674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33674
  have eq200266 : (M.op x y) = (M.op x x) ∨ y = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq200242
    | exact resolve eq200242 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq200242
  have eq201296 : (M.op x y) = (k (M.op x y) x) ∨ y = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq200266
  have eq202922 : y ≠ (M.op x y) ∨ y = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq201296
  have eq202932 : y = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq202922
       have r₂ := eq26581
       grind)
    | exact resolve eq202922 eq26581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26581 eq202922
  have eq203007 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq202932 eq26580
    | exact resolve eq26580 eq202932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202932
  have eq203014 : (σ y) = (σ (k y x)) ∨ x = (M.op x y) := by grind
  clear eq203007
  have eq203028 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq203014
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq203014
    | exact resolve eq203014 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203014
  have eq203051 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq203028
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq203028
    | exact resolve eq203028 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203028
  have eq203189 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26394 eq203051
    | exact resolve eq203051 eq26394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203051
  have eq203230 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq203189
  have eq203256 : (τ (σ (M.op x y))) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq203230 eq135
    | exact resolve eq135 eq203230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135 eq203230
  have eq203301 : (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq203256
    | exact resolve eq203256 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq203256
  have eq203345 : (σ (M.op x y)) = (σ (k y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq203301 eq26580
    | exact resolve eq26580 eq203301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26580 eq203301
  have eq203352 : (σ (M.op x y)) = (σ (k y x)) ∨ x = (M.op x y) := by grind
  clear eq203345
  have eq203369 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq203352
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq203352
    | exact resolve eq203352 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq203352
  have eq203391 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq203369
    | exact resolve eq203369 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203369
  have eq203914 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq203391 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq203391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203391
  have eq203934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq203914
    | exact resolve eq203914 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203914
  have eq203947 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq203934
       have r₂ := eq28
       grind)
    | exact resolve eq203934 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203934
  have eq223917 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26394 eq203947
    | exact resolve eq203947 eq26394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26394 eq203947
  have eq223989 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq223917
  have eq224073 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq223989 eq18366
    | exact resolve eq18366 eq223989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18366 eq223989
  have eq224075 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq224073
  have eq224130 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq224075 eq6497
    | exact resolve eq6497 eq224075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6497 eq224075
  have eq225036 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq33170 eq224130
    | exact resolve eq224130 eq33170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33170 eq224130
  have eq225104 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op x y) := by grind
  clear eq225036
  have eq225114 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq225104 eq26397
    | exact resolve eq26397 eq225104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26397 eq225104
  have eq225162 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq225114
  have eq225164 : x = (M.op x y) := by
    first
    | (have r₁ := eq225162
       have r₂ := eq28
       grind)
    | exact resolve eq225162 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225162
  have eq225167 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq225164 eq21
    | exact resolve eq21 eq225164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq225326 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq225164 eq3407
    | exact resolve eq3407 eq225164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3407
  have eq225439 : y = (k x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq225164 eq197742
    | exact resolve eq197742 eq225164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197742
  have eq225455 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq225326
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq225326
    | exact resolve eq225326 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq225326
  have eq225599 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq225167
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq225167
    | exact resolve eq225167 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225167
  have eq225602 : x = (M.op y y) := by
    first
    | exact superpose eq225164 eq225455
    | exact resolve eq225455 eq225164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225164 eq225455
  have eq225603 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq225599 eq27
    | exact resolve eq27 eq225599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225792 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq225599 eq197836
    | exact resolve eq197836 eq225599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197836
  have eq225991 : x = (k x y) := by grind
  clear eq225602
  have eq226158 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq225991
       grind)
    | exact superpose eq225991 eq45
    | exact resolve eq45 eq225991
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq225991
  have eq226202 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq225599 eq226158
    | exact resolve eq226158 eq225599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226158
  have eq226222 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq226202
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq226202
    | exact resolve eq226202 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226202
  have eq226240 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq225599 eq226222
    | exact resolve eq226222 eq225599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226222
  have eq236903 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq580 x
       have i₂ := eq225439
       grind)
    | exact superpose eq225439 eq580
    | (have j0 := eq580 x
       grind)
    | exact resolve eq580 eq225439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580 eq225439
  have eq236963 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq236903
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq236903
    | exact resolve eq236903 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq236903
  have eq237003 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq236963
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq236963
    | exact resolve eq236963 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236963
  have eq237043 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq27 eq237003
    | exact resolve eq237003 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq237003
  have eq237067 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq225599 eq237043
    | exact resolve eq237043 eq225599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237043
  have eq237087 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq237067
       have r₂ := eq28
       grind)
    | exact resolve eq237067 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237067
  have eq237093 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq237087
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq237087
    | exact resolve eq237087 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq237087
  have eq237098 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq225599 eq237093
    | exact resolve eq237093 eq225599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225599 eq237093
  have eq237359 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq237098
  have eq241253 : (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq237359 eq225792
    | exact resolve eq225792 eq237359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225792 eq237359
  have eq241300 : (σ (M.op x y)) = (σ y) := by grind
  clear eq241253
  have eq241658 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq241300 eq225603
    | exact resolve eq225603 eq241300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225603
  have eq241661 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq241300 eq226240
    | exact resolve eq226240 eq241300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226240 eq241300
  have eq244723 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq241661 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq241661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241661
  have eq244724 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq244723
  have eq244742 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq241658 eq244724
    | exact resolve eq244724 eq241658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241658 eq244724
  have eq244772 : False := by grind
  exact eq244772

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then X else if m(X,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_x_pyy_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
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
  have eq29 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 (τ X0))
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq57 : ∀ X1 : G, (M.op X1 (M.op X1 X1)) = X1 := by
    intro X1
    first
    | (have i₁ := eq9 X1 (M.op x (M.op X1 x)) X1
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq57 X0
       grind)
    | exact superpose eq57 eq9
    | exact resolve eq9 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op (M.op X0 X0) X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X2 X1
       have i₂ := eq59 X0 X0
       grind)
    | exact superpose eq59 eq9
    | exact resolve eq9 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq68 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 (M.op X0 X0)
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq9
    | exact resolve eq9 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq67 (τ X0)
       grind)
    | exact superpose eq67 eq18
    | exact resolve eq18 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq71
    | exact resolve eq71 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq81 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (σ (M.op (τ (τ X0)) (τ (τ X0))))
       have i₂ := eq72 (τ X0)
       grind)
    | exact superpose eq72 eq18
    | exact resolve eq18 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq72
  have eq82 : ∀ X0 : G, (k X0 (σ (σ (M.op (τ (τ X0)) (τ (τ X0)))))) = X0 := by
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
  have eq108 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X1) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 (M.op X1 X0) (M.op X1 X1) X2
       have i₂ := eq9 X1 (M.op X1 X0) X0
       grind)
    | exact superpose eq9 eq66
    | exact resolve eq66 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq66 X0 (M.op X0 X0) X1
       have i₂ := eq59 X0 X0
       grind)
    | exact superpose eq59 eq66
    | exact resolve eq66 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq109 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq109 X0 X1
       have i₂ := eq14 (M.op X1 X0) X1
       grind)
    | exact superpose eq14 eq109
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq109 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq357 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq377 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq369 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq369
    | (have j0 := eq369 (σ X0) (σ X1)
       grind)
    | exact resolve eq369 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq381 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq369 (τ X1) (τ X0)
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq369
    | (have j0 := eq369 (τ X1) (τ X0)
       grind)
    | exact resolve eq369 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq388 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op (σ X1) X0)) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq369 X0 (σ X1)
       grind)
    | exact superpose eq369 eq23
    | (have j1 := eq369 X0 (σ X1)
       grind)
    | exact resolve eq23 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq389 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq369 X0 (τ X1)
       grind)
    | exact superpose eq369 eq19
    | (have j1 := eq369 X0 (τ X1)
       grind)
    | exact resolve eq19 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq509 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X2 (M.op X1 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq66 X0 (M.op (M.op X1 X0) (M.op X1 X0)) X2
       have i₂ := eq68 X0 X1 X0
       grind)
    | exact superpose eq68 eq66
    | exact resolve eq66 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq554 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X2 (M.op X1 X0))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq108 (M.op X0 X0) (M.op X1 (M.op X0 X2)) X2
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq108
    | exact resolve eq108 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq557 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X1) (M.op X2 X1)) = (M.op (M.op X3 (M.op X0 X1)) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq108 (M.op (M.op X1 X0) (M.op X1 X0)) (M.op X2 X0) X2
       have i₂ := eq68 X0 X1 X2
       grind)
    | exact superpose eq68 eq108
    | exact resolve eq108 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op (M.op X3 X1) (M.op (M.op X0 X2) (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq68 X1 X2 X3
       have i₂ := eq108 X1 X2 X0
       grind)
    | (have i₁ := eq68 X0 X0 X2
       have i₂ := eq108 X0 X0 X0
       grind)
    | exact superpose eq108 eq68
    | exact resolve eq68 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq569 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op X2 X1) (M.op (M.op X0 X2) (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq57 (M.op X2 X1)
       have i₂ := eq108 X1 X2 X0
       grind)
    | (have i₁ := eq57 (M.op X0 X0)
       have i₂ := eq108 X0 X0 X0
       grind)
    | exact superpose eq108 eq57
    | exact resolve eq57 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq622 : ∀ X1 X2 : G, (M.op X2 X2) = (M.op (M.op X2 X1) X2) := by
    intro X1 X2
    first
    | (have i₁ := eq554 X1 X2 (M.op X2 X1) (M.op x X1)
       have i₂ := eq68 X1 X2 x
       grind)
    | exact superpose eq68 eq554
    | exact resolve eq554 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq650 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) (M.op X2 (M.op X1 X0))) = (M.op X1 (M.op X2 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq622 (M.op X1 X1) (M.op X2 (M.op X1 X0))
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq622
    | exact resolve eq622 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq651 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq622 (M.op X0 X0) (M.op X1 X0)
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq622
    | exact resolve eq622 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X1) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq622 (M.op (M.op X2 X1) (M.op X2 X1)) (M.op X0 X1)
       have i₂ := eq68 X1 X2 X0
       grind)
    | exact superpose eq68 eq622
    | exact resolve eq622 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X1 X0))) = (M.op (M.op X1 X0) (M.op X2 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq650 X0 X1 X2
       have i₂ := eq651 (M.op X1 X0) X2
       grind)
    | exact superpose eq651 eq650
    | exact resolve eq650 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq650
  have eq762 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq108 X0 X1 X2
       have i₂ := eq651 X0 X1
       grind)
    | exact superpose eq651 eq108
    | exact resolve eq108 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq763 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq68 X0 X1 X2
       have i₂ := eq651 X0 X1
       grind)
    | exact superpose eq651 eq68
    | exact resolve eq68 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq774 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq57 (M.op X1 X0)
       have i₂ := eq651 X0 X1
       grind)
    | exact superpose eq651 eq57
    | exact resolve eq57 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq775 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 (M.op X1 X0) X2
       have i₂ := eq651 X0 X1
       grind)
    | exact superpose eq651 eq59
    | exact resolve eq59 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq789 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq774 X0 X1
       have i₂ := eq674 X0 X1 X0
       grind)
    | exact superpose eq674 eq774
    | exact resolve eq774 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq854 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X2 (M.op X1 X0)) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq762 X0 (M.op X1 X0) X2
       have i₂ := eq109 X0 X1
       grind)
    | exact superpose eq109 eq762
    | exact resolve eq762 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq860 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X0 X2)) (M.op X1 (M.op X2 X1))) = (M.op (M.op X2 X1) (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq762 (M.op X1 X0) (M.op X2 X1) X2
       have i₂ := eq762 X0 X1 X2
       grind)
    | (have i₁ := eq762 (M.op X1 X0) X0 X2
       have i₂ := eq762 X0 X1 X2
       grind)
    | exact superpose eq762 eq762
    | exact resolve eq762 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq919 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op (M.op X3 (M.op X0 X2)) (M.op X1 (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq860 X0 X1 X2 X3
       have i₂ := eq763 X1 X2 X2
       grind)
    | exact superpose eq763 eq860
    | exact resolve eq860 eq763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763 eq860
  have eq925 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X1 X0)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq854 X0 X1 X2
       have i₂ := eq57 X0
       grind)
    | (have i₁ := eq854 X0 X1 X2
       have i₂ := eq57 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq57 eq854
    | exact resolve eq854 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq854
  have eq966 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X2 X1))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq108 (M.op X0 X0) (M.op X2 (M.op X1 X0)) X2
       have i₂ := eq925 X0 X1 X2
       grind)
    | exact superpose eq925 eq108
    | exact resolve eq108 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq968 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X2 X1)) (M.op X0 (M.op X2 X1))) = (M.op (M.op X3 (M.op X4 X1)) (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq554 (M.op X1 X1) (M.op X0 (M.op X2 X1)) X4 X3
       have i₂ := eq925 X1 X2 X0
       grind)
    | exact superpose eq925 eq554
    | exact resolve eq554 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq969 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X2 X1)) (M.op X0 (M.op X2 X1))) = (M.op X1 (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq622 (M.op X1 X1) (M.op X0 (M.op X2 X1))
       have i₂ := eq925 X1 X2 X0
       grind)
    | exact superpose eq925 eq622
    | exact resolve eq622 eq925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq925
  have eq976 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X2 X1))) = (M.op X1 (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq969 X0 X1 X2
       have i₂ := eq651 (M.op X2 X1) X0
       grind)
    | exact superpose eq651 eq969
    | exact resolve eq969 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq977 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X2 X1))) = (M.op (M.op X3 (M.op X4 X1)) (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq968 X0 X1 X2 X3 X4
       have i₂ := eq651 (M.op X2 X1) X0
       grind)
    | exact superpose eq651 eq968
    | exact resolve eq968 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968
  have eq979 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X3 (M.op X4 X1)) (M.op X0 (M.op X2 X1))) = (M.op X1 (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq977 X0 X1 X2 X3 X4
       have i₂ := eq976 X0 X1 X2
       grind)
    | exact superpose eq976 eq977
    | exact resolve eq977 eq976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq976 eq977
  have eq1308 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X3 X3)) = (M.op (M.op X4 (M.op X1 (M.op X0 (M.op X2 X3)))) (M.op X3 X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq762 X1 (M.op X3 (M.op X0 (M.op X2 X1))) X2
       have i₂ := eq966 X0 X1 X2 X3
       grind)
    | exact superpose eq966 eq762
    | exact resolve eq762 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1325 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op X1 (M.op X0 (M.op X2 X3)))) (M.op X3 X3)) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1308 X0 X1 X2 X3 X4
       have i₂ := eq57 X3
       grind)
    | (have i₁ := eq1308 X0 X1 X2 X3 X4
       have i₂ := eq57 (M.op X3 (M.op X3 X3))
       grind)
    | exact superpose eq57 eq1308
    | exact resolve eq1308 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308
  have eq1681 : ∀ X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X1 X3)) (M.op X2 X3))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq569 x (M.op (M.op x X2) (M.op X2 X1)) (M.op X3 X1)
       have i₂ := eq562 x X1 X2 X3
       grind)
    | exact superpose eq562 eq569
    | exact resolve eq569 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq1696 : ∀ X1 X2 X3 X4 : G, (M.op X2 X3) = (M.op X2 (M.op (M.op X4 (M.op X1 X3)) (M.op X2 X3))) := by
    intro X1 X2 X3 X4
    first
    | (have i₁ := eq1681 X1 X2 X3 X4
       have i₂ := eq674 X3 X2 (M.op X4 (M.op X1 X3))
       grind)
    | exact superpose eq674 eq1681
    | exact resolve eq1681 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1681
  have eq2254 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq653 X1 X0 X2
       have i₂ := eq651 X0 X1
       grind)
    | exact superpose eq651 eq653
    | exact resolve eq653 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651 eq653
  have eq2555 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X1) = (M.op (M.op X4 (M.op X2 X1)) (M.op (M.op (M.op X0 (M.op X3 X1)) (M.op X2 X1)) (M.op X2 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq775 (M.op (M.op X4 (M.op X1 X3)) (M.op X2 X3)) X2 X2
       have i₂ := eq1696 X1 X2 X3 X4
       grind)
    | exact superpose eq1696 eq775
    | exact resolve eq775 eq1696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775 eq1696
  have eq2562 : ∀ X0 X1 X2 X3 : G, (M.op X2 X1) = (M.op X1 (M.op (M.op (M.op X0 (M.op X3 X1)) (M.op X2 X1)) (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2555 X0 X1 X2 X3 x
       have i₂ := eq979 (M.op (M.op X0 (M.op X3 X1)) (M.op X2 X1)) X1 X2 x X2
       grind)
    | exact superpose eq979 eq2555
    | exact resolve eq2555 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2555
  have eq2578 : ∀ X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op (M.op X2 X1) (M.op X2 X1))) := by
    intro X1 X2
    first
    | (have i₁ := eq2562 x X1 X2 x
       have i₂ := eq557 X2 X1 X2 (M.op x (M.op x X1))
       grind)
    | exact superpose eq557 eq2562
    | exact resolve eq2562 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2562
  have eq2590 : ∀ X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op X1 (M.op X2 X1))) := by
    intro X1 X2
    first
    | (have i₁ := eq2578 X1 X2
       have i₂ := eq2254 X1 X2 X2
       grind)
    | exact superpose eq2254 eq2578
    | exact resolve eq2578 eq2254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2578
  have eq2623 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op (M.op X0 X2) (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2590 X1 X2
       have i₂ := eq762 X1 X2 X0
       grind)
    | (have i₁ := eq2590 (M.op X2 X1) X1
       have i₂ := eq762 (M.op X2 X1) X1 X2
       grind)
    | exact superpose eq762 eq2590
    | exact resolve eq2590 eq762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3328 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 X3) = (M.op (M.op X5 (M.op X4 (M.op X1 (M.op X0 (M.op X2 X3))))) (M.op X3 (M.op X3 X3))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq919 X0 X1 (M.op X3 (M.op X0 (M.op X2 X1))) X3
       have i₂ := eq966 X0 X1 X2 X3
       grind)
    | exact superpose eq966 eq919
    | exact resolve eq919 eq966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq966
  have eq3440 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 X3) = (M.op (M.op X5 (M.op X4 (M.op X1 (M.op X0 (M.op X2 X3))))) X3) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq3328 X0 X1 X2 X3 X4 X5
       have i₂ := eq57 X3
       grind)
    | (have i₁ := eq3328 X0 X1 X2 X3 X4 X5
       have i₂ := eq57 (M.op X3 (M.op X3 X3))
       grind)
    | exact superpose eq57 eq3328
    | exact resolve eq3328 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3328
  have eq4167 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X6 (M.op X5 (M.op X0 (M.op X4 (M.op X1 (M.op X3 X2)))))) (M.op (M.op X2 X2) X2)) = X2 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq919 X0 (M.op X3 X3) (M.op X4 (M.op X1 (M.op X0 (M.op X2 X3)))) X3
       have i₂ := eq1325 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq1325 eq919
    | exact resolve eq919 eq1325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq919 eq1325
  have eq4183 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op X6 (M.op X5 (M.op X0 (M.op X4 (M.op X1 (M.op X3 X2)))))) (M.op X2 X2)) = X2 := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq4167 X0 X1 X2 X3 X4 X5 X6
       have i₂ := eq109 X2 X2
       grind)
    | exact superpose eq109 eq4167
    | exact resolve eq4167 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq4167
  have eq4984 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq388 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq388
    | exact resolve eq388 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq5030 : ∀ X0 X1 : G, (τ (k X1 X0)) = (τ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4984 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq4984
    | (have j0 := eq4984 X0 X1
       grind)
    | exact resolve eq4984 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4984
  have eq5073 : ∀ X0 X1 X2 : G, (τ (k (k X1 X0) X2)) = (k (τ (M.op X0 X1)) (τ X2)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X2 (k X1 X0)
       have i₂ := eq5030 X0 X1
       grind)
    | exact superpose eq5030 eq31
    | (have j1 := eq5030 X0 X1
       grind)
    | exact resolve eq31 eq5030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5030
  have eq5077 : ∀ X0 X1 X2 : G, (τ (k (k X1 X0) X2)) = (τ (k (M.op X0 X1) X2)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5073 X0 X1 X2
       have i₂ := eq31 X2 (M.op X0 X1)
       grind)
    | exact superpose eq31 eq5073
    | (have j0 := eq5073 X0 X1 X2
       grind)
    | exact resolve eq5073 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5073
  have eq5088 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq389 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq389
    | exact resolve eq389 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5113 : ∀ X0 : G, (k X0 (σ (k (σ (τ (τ X0))) (τ X0)))) = X0 ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq389 (τ (τ X0)) (τ X0)
       grind)
    | exact superpose eq389 eq82
    | (have j1 := eq389 (τ (τ X0)) (τ X0)
       grind)
    | exact resolve eq82 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq389
  have eq5149 : ∀ X0 : G, (k X0 (k (σ (σ (τ (τ X0)))) X0)) = X0 ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5113 X0
       have i₂ := eq19 X0 (σ (τ (τ X0)))
       grind)
    | exact superpose eq19 eq5113
    | (have j0 := eq5113 X0
       grind)
    | exact resolve eq5113 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5113
  have eq5160 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5088 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq5088
    | (have j0 := eq5088 X0 X1
       grind)
    | exact resolve eq5088 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5088
  have eq5162 : ∀ X0 : G, (k X0 (k (σ (τ X0)) X0)) = X0 ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5149 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq5149
    | (have j0 := eq5149 X0
       grind)
    | exact resolve eq5149 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5149
  have eq5164 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5162 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5162
    | (have j0 := eq5162 X0
       grind)
    | exact resolve eq5162 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5162
  have eq8074 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X2 X1))) = (M.op (M.op X3 X0) (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq762 (M.op X2 X1) X0 X3
       have i₂ := eq674 X1 X2 X0
       grind)
    | exact superpose eq674 eq762
    | exact resolve eq762 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8078 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 X1)) = (M.op X0 (M.op X2 (M.op X0 (M.op X2 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq789 (M.op X2 X1) X0
       have i₂ := eq674 X1 X2 X0
       grind)
    | exact superpose eq674 eq789
    | exact resolve eq789 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq8858 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op (M.op X0 (M.op X1 (M.op X0 X2))) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq674 (M.op X0 (M.op X2 X1)) X2 X0
       have i₂ := eq8078 X0 X1 X2
       grind)
    | exact superpose eq8078 eq674
    | exact resolve eq674 eq8078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq8927 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8858 X0 X1 X2
       have i₂ := eq557 X1 (M.op X0 X2) X1 X0
       grind)
    | exact superpose eq557 eq8858
    | exact resolve eq8858 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq8858
  have eq8961 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op X2 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq8927 X0 X1 X2
       have i₂ := eq979 X1 X2 X0 X1 X0
       grind)
    | exact superpose eq979 eq8927
    | exact resolve eq8927 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8927
  have eq13210 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op X0 X2)) = (M.op (M.op X3 X2) (M.op X0 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq8074 X1 (M.op X2 X1) (M.op X0 X2) X3
       have i₂ := eq2623 X0 X1 X2
       grind)
    | exact superpose eq2623 eq8074
    | exact resolve eq8074 eq2623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8074
  have eq29362 : ∀ X0 : G, (τ (τ X0)) = (k (τ (τ X0)) (τ (τ X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq67 (τ (τ X0))
       have i₂ := eq5164 X0
       grind)
    | exact superpose eq5164 eq67
    | (have j1 := eq5164 X0
       grind)
    | exact resolve eq67 eq5164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq5164
  have eq29470 : ∀ X0 : G, (τ (τ X0)) = (τ (k (τ X0) (τ X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq29362 X0
       have i₂ := eq31 (τ X0) (τ X0)
       grind)
    | exact superpose eq31 eq29362
    | (have j0 := eq29362 X0
       grind)
    | exact resolve eq29362 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29362
  have eq29479 : ∀ X0 : G, (τ (τ X0)) = (τ (τ (k X0 X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq29470 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq29470
    | (have j0 := eq29470 X0
       grind)
    | exact resolve eq29470 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29470
  have eq29514 : ∀ X0 X1 : G, (k (τ X1) (τ (τ X0))) = (τ (k X1 (τ (k X0 X0)))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31 (τ (k X0 X0)) X1
       have i₂ := eq29479 X0
       grind)
    | exact superpose eq29479 eq31
    | (have j1 := eq29479 X0
       grind)
    | exact resolve eq31 eq29479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29544 : ∀ X0 X1 : G, (τ (k X1 (τ X0))) = (τ (k X1 (τ (k X0 X0)))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq29514 X0 X1
       have i₂ := eq31 (τ X0) X1
       grind)
    | exact superpose eq31 eq29514
    | (have j0 := eq29514 X0 X1
       grind)
    | exact resolve eq29514 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29514
  have eq31181 : ∀ X0 X1 X2 : G, (k (k X2 X1) X0) = (σ (τ (k (M.op X1 X2) X0))) ∨ (M.op X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11 (k (k X2 X1) X0)
       have i₂ := eq5077 X1 X2 X0
       grind)
    | exact superpose eq5077 eq11
    | (have j1 := eq5077 X1 X2 X2
       grind)
    | exact resolve eq11 eq5077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5077
  have eq31209 : ∀ X0 X1 X2 : G, (k (M.op X1 X2) X0) = (k (k X2 X1) X0) ∨ (M.op X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31181 X0 X1 X2
       have i₂ := eq11 (k (M.op X1 X2) X0)
       grind)
    | exact superpose eq11 eq31181
    | (have j0 := eq31181 X0 X1 X2
       grind)
    | exact resolve eq31181 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31181
  have eq134157 : ∀ X0 X1 : G, (k X1 (τ (k X0 X0))) = (σ (τ (k X1 (τ X0)))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 (τ (k X0 X0)))
       have i₂ := eq29544 X0 X1
       grind)
    | exact superpose eq29544 eq11
    | (have j1 := eq29544 X0 X1
       grind)
    | exact resolve eq11 eq29544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29544
  have eq134361 : ∀ X0 X1 : G, (k X1 (τ X0)) = (k X1 (τ (k X0 X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq134157 X0 X1
       have i₂ := eq11 (k X1 (τ X0))
       grind)
    | exact superpose eq11 eq134157
    | (have j0 := eq134157 X0 X1
       grind)
    | exact resolve eq134157 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134157
  have eq134524 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 (k X0 X0) X1
       have i₂ := eq134361 X0 X1
       grind)
    | exact superpose eq134361 eq19
    | (have j1 := eq134361 X0 X1
       grind)
    | exact resolve eq19 eq134361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134361
  have eq134694 : ∀ X0 X1 : G, (k (σ X1) X0) = (k (σ X1) (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq134524 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq134524
    | (have j0 := eq134524 X0 X1
       grind)
    | exact resolve eq134524 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq134524
  have eq134737 : ∀ X0 X1 : G, (k X0 X1) = (k X0 (k X1 X1)) ∨ (k X1 (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq134694 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq134694
    | (have j0 := eq134694 X1 X1
       grind)
    | exact resolve eq134694 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134694
  have eq135587 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq134737 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134737
  have eq135659 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (k (τ X0) (τ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq135587 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq135587
    | exact resolve eq135587 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135587
  have eq135674 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (τ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq135659 X0
       have i₂ := eq31 (k X0 X0) X0
       grind)
    | exact superpose eq31 eq135659
    | (have j0 := eq135659 X0
       grind)
    | exact resolve eq135659 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135659
  have eq135925 : ∀ X0 : G, (τ (τ X0)) ≠ (τ (τ (k X0 X0))) ∨ (τ (τ X0)) = (τ (k (τ X0) (τ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq135674 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq135674
    | exact resolve eq135674 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135674
  have eq135959 : ∀ X0 : G, (τ (τ X0)) ≠ (τ (τ (k X0 X0))) ∨ (τ (τ X0)) = (τ (τ (k X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq135925 X0
       have i₂ := eq31 (k X0 X0) X0
       grind)
    | exact superpose eq31 eq135925
    | (have j0 := eq135925 X0
       grind)
    | exact resolve eq135925 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135925
  have eq256784 : ∀ X0 : G, (τ (τ X0)) ≠ (τ (τ X0)) ∨ (τ (τ X0)) = (τ (τ (k X0 (k X0 X0)))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq135959 X0
       have i₂ := eq29479 X0
       grind)
    | exact superpose eq29479 eq135959
    | (have j0 := eq135959 X0
       have j1 := eq29479 X0
       grind)
    | (have r₁ := eq135959 X0
       have r₂ := eq29479 X0
       grind)
    | exact resolve eq135959 eq29479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29479 eq135959
  have eq256790 : ∀ X0 : G, (τ (τ X0)) = (τ (τ (k X0 (k X0 X0)))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq256784 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256784
  have eq256911 : ∀ X0 : G, (τ (k X0 (k X0 X0))) = (σ (τ (τ X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (τ (k X0 (k X0 X0)))
       have i₂ := eq256790 X0
       grind)
    | exact superpose eq256790 eq11
    | (have j1 := eq256790 X0
       grind)
    | exact resolve eq11 eq256790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256790
  have eq257066 : ∀ X0 : G, (τ X0) = (τ (k X0 (k X0 X0))) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq256911 X0
       have i₂ := eq11 (τ X0)
       grind)
    | exact superpose eq11 eq256911
    | (have j0 := eq256911 X0
       grind)
    | exact resolve eq256911 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256911
  have eq258183 : ∀ X0 : G, (σ (τ X0)) = (k X0 (k X0 X0)) ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 (k X0 (k X0 X0))
       have i₂ := eq257066 X0
       grind)
    | exact superpose eq257066 eq11
    | (have j1 := eq257066 X0
       grind)
    | exact resolve eq11 eq257066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257066
  have eq258341 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq258183 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq258183
    | (have j0 := eq258183 X0
       grind)
    | exact resolve eq258183 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258183
  have eq258342 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq258341 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258341
  have eq258420 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq369 X0 (k X0 X0)
       have i₂ := eq258342 X0
       grind)
    | exact superpose eq258342 eq369
    | (have j0 := eq369 X0 (k X0 X0)
       grind)
    | exact resolve eq369 eq258342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369
  have eq258434 : ∀ X0 X1 : G, (k X0 X1) = (k (M.op (k X0 X0) X0) X1) ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31209 X1 (k X0 X0) X0
       have i₂ := eq258342 X0
       grind)
    | exact superpose eq258342 eq31209
    | (have j0 := eq31209 X0 (k X0 X0) X0
       grind)
    | exact resolve eq31209 eq258342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31209
  have eq258647 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op (k X0 X0) (M.op X1 X0))) ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8078 X0 X0 (k X0 X0)
       have i₂ := eq258420 X0
       grind)
    | exact superpose eq258420 eq8078
    | (have j1 := eq258420 X0
       grind)
    | exact resolve eq8078 eq258420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8078
  have eq320044 : ∀ X0 : G, (M.op (k X0 X0) (M.op (k X0 X0) X0)) = X0 ∨ (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq258647 X0 (k X0 X0)
       have i₂ := eq258420 X0
       grind)
    | exact superpose eq258420 eq258647
    | (have j0 := eq258647 X0 x
       have j1 := eq258420 X0
       grind)
    | exact resolve eq258647 eq258420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258420 eq258647
  have eq320728 : ∀ X0 : G, (M.op (k X0 X0) (M.op (k X0 X0) X0)) = X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq320044 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320044
  have eq321037 : ∀ X0 : G, (M.op X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq8961 (k X0 X0) (k X0 X0) X0
       have i₂ := eq320728 X0
       grind)
    | exact superpose eq320728 eq8961
    | (have j1 := eq320728 X0
       grind)
    | exact resolve eq8961 eq320728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8961 eq320728
  have eq332835 : ∀ X0 X1 : G, (k X0 X1) = (k (M.op X0 X0) X1) ∨ (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq258434 X0 X1
       have i₂ := eq321037 X0
       grind)
    | exact superpose eq321037 eq258434
    | (have j0 := eq258434 X0 X1
       have j1 := eq321037 X0
       grind)
    | exact resolve eq258434 eq321037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258434 eq321037
  have eq333309 : ∀ X0 X1 : G, (k X0 X1) = (k (M.op X0 X0) X1) ∨ (M.op X0 (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq332835 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332835
  have eq336655 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq333309
  have eq337980 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (k X0 X0)
       have i₂ := eq336655 X0
       grind)
    | exact superpose eq336655 eq13
    | (have j0 := eq13 X0 (k X0 X0)
       have j1 := eq336655 X0
       grind)
    | (have r₁ := eq13 X0 (k X0 X0)
       have r₂ := eq336655 X0
       grind)
    | exact resolve eq13 eq336655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336655
  have eq338247 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 (k X0 X0)) = (M.op (k X0 X0) (k X0 X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq337980 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337980
  have eq338296 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq338247 X0
       have i₂ := eq258342 X0
       grind)
    | exact superpose eq258342 eq338247
    | (have j0 := eq338247 X0
       grind)
    | exact resolve eq338247 eq258342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258342 eq338247
  have eq338297 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq338296 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338296
  have eq364858 : ∀ X0 X1 X2 X3 X4 X5 : G, (k X0 X0) = (M.op (M.op X2 (M.op X1 (M.op X4 (M.op X3 (M.op X5 X0))))) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq4183 X0 X1 (k X0 X0) (k X0 X0) X4 X5 x
       have i₂ := eq338297 X0
       grind)
    | exact superpose eq338297 eq4183
    | (have j1 := eq338297 X0
       grind)
    | exact resolve eq4183 eq338297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4183 eq338297
  have eq365016 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq364858 X0 x x x x x
       have i₂ := eq3440 x x x X0 x x
       grind)
    | exact superpose eq3440 eq364858
    | (have j0 := eq364858 X0 x x x x x
       grind)
    | exact resolve eq364858 eq3440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3440 eq364858
  have eq365017 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq365016 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365016
  have eq365056 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq365017 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq365017
    | exact resolve eq365017 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365057 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq365017 (τ X0)
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq365017
    | exact resolve eq365017 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq365594 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq365057 X0
       have i₂ := eq365017 X0
       grind)
    | exact superpose eq365017 eq365057
    | exact resolve eq365057 eq365017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365057
  have eq365595 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq365056 X0
       have i₂ := eq365017 X0
       grind)
    | exact superpose eq365017 eq365056
    | exact resolve eq365056 eq365017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365017 eq365056
  have eq365719 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq57 (τ X0)
       have i₂ := eq365594 X0
       grind)
    | exact superpose eq365594 eq57
    | exact resolve eq57 eq365594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365783 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq622 (τ X0) (τ X0)
       have i₂ := eq365594 X0
       grind)
    | exact superpose eq365594 eq622
    | exact resolve eq622 eq365594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq365807 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op X1 (M.op (τ (M.op X0 X0)) (M.op (τ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq2623 (τ X0) X1 (τ X0)
       have i₂ := eq365594 X0
       grind)
    | exact superpose eq365594 eq2623
    | exact resolve eq2623 eq365594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2623
  have eq366090 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq57 (σ X0)
       have i₂ := eq365595 X0
       grind)
    | exact superpose eq365595 eq57
    | exact resolve eq57 eq365595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366410 : ∀ X0 X1 X2 : G, (τ (M.op X1 X0)) = (M.op (τ (M.op X1 X0)) (τ (M.op (M.op X2 X1) (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq365719 (M.op X1 X0)
       have i₂ := eq13210 X1 X2 X0 X1
       grind)
    | (have i₁ := eq365719 (M.op X2 X2)
       have i₂ := eq13210 X2 X2 X2 x
       grind)
    | exact superpose eq13210 eq365719
    | exact resolve eq365719 eq13210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13210
  have eq366413 : ∀ X0 : G, (τ (τ X0)) = (M.op (τ (τ X0)) (τ (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq365719 (τ X0)
       have i₂ := eq365594 X0
       grind)
    | exact superpose eq365594 eq365719
    | exact resolve eq365719 eq365594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365719
  have eq367676 : ∀ X0 X1 : G, (M.op (τ (τ (M.op X0 X0))) (τ (τ (M.op X0 X0)))) = (M.op (M.op X1 (τ (τ X0))) (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq509 (τ (τ (M.op X0 X0))) (τ (τ X0)) X1
       have i₂ := eq366413 X0
       grind)
    | exact superpose eq366413 eq509
    | exact resolve eq509 eq366413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509 eq366413
  have eq367883 : ∀ X0 X1 : G, (M.op (M.op X1 (τ (τ X0))) (τ (τ (M.op X0 X0)))) = (τ (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq367676 X0 X1
       have i₂ := eq365594 (τ (M.op X0 X0))
       grind)
    | exact superpose eq365594 eq367676
    | exact resolve eq367676 eq365594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367676
  have eq367918 : ∀ X0 X1 : G, (τ (τ (M.op (M.op X0 X0) (M.op X0 X0)))) = (M.op (M.op X1 (τ (τ X0))) (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq367883 X0 X1
       have i₂ := eq365594 (M.op X0 X0)
       grind)
    | exact superpose eq365594 eq367883
    | exact resolve eq367883 eq365594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367883
  have eq367938 : ∀ X0 X1 : G, (τ (τ X0)) = (M.op (M.op X1 (τ (τ X0))) (τ (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq367918 X0 X1
       have i₂ := eq59 X0 X0
       grind)
    | exact superpose eq59 eq367918
    | exact resolve eq367918 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq367918
  have eq369753 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (τ (τ (M.op (σ X0) (σ X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq367938 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq367938
    | exact resolve eq367938 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367938
  have eq370053 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (τ (τ (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq369753 X0 X1
       have i₂ := eq365595 X0
       grind)
    | exact superpose eq365595 eq369753
    | exact resolve eq369753 eq365595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369753
  have eq370097 : ∀ X0 X1 : G, (τ X0) = (M.op (M.op X1 (τ X0)) (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq370053 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq370053
    | exact resolve eq370053 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370053
  have eq370177 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) = (M.op (M.op X2 (τ (M.op X0 X1))) (τ (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq370097 (M.op X0 X1) X2
       have i₂ := eq2254 X1 X0 X0
       grind)
    | exact superpose eq2254 eq370097
    | exact resolve eq370097 eq2254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370097
  have eq376908 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X0) (M.op (τ (M.op X1 X1)) (τ X1))) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq365807 X1 (τ X0)
       have i₂ := eq381 X0 X1
       grind)
    | exact superpose eq381 eq365807
    | (have j1 := eq381 X0 X1
       grind)
    | exact resolve eq365807 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381 eq365807
  have eq377305 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X0) (τ (M.op X1 X1))) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq376908 X0 X1
       have i₂ := eq365783 X1
       grind)
    | exact superpose eq365783 eq376908
    | (have j0 := eq376908 X0 X1
       grind)
    | exact resolve eq376908 eq365783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365783 eq376908
  have eq423145 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X2) (M.op X2 X1))) = (M.op (τ (M.op X2 X1)) (τ (M.op (M.op X2 X1) (M.op (M.op X0 X2) (M.op X2 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq370177 (M.op X0 X2) (M.op X2 X1) (τ (M.op X2 X1))
       have i₂ := eq366410 X1 X2 X0
       grind)
    | exact superpose eq366410 eq370177
    | exact resolve eq370177 eq366410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366410 eq370177
  have eq423801 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X0 X2) (M.op X2 X1))) = (M.op (τ (M.op X2 X1)) (τ (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq423145 X0 X1 X2
       have i₂ := eq569 X0 X1 X2
       grind)
    | exact superpose eq569 eq423145
    | exact resolve eq423145 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569 eq423145
  have eq423867 : ∀ X0 X1 X2 : G, (τ (M.op (M.op X2 X1) (M.op X2 X1))) = (τ (M.op (M.op X0 X2) (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq423801 X0 X1 X2
       have i₂ := eq365594 (M.op X2 X1)
       grind)
    | exact superpose eq365594 eq423801
    | exact resolve eq423801 eq365594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423801
  have eq423912 : ∀ X0 X1 X2 : G, (τ (M.op X1 (M.op X2 X1))) = (τ (M.op (M.op X0 X2) (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq423867 X0 X1 X2
       have i₂ := eq2254 X1 X2 X2
       grind)
    | exact superpose eq2254 eq423867
    | exact resolve eq423867 eq2254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2254 eq423867
  have eq1339466 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ X1) (τ (σ (M.op X0 X0)))) ∨ (τ (k (σ X0) X1)) = (M.op (τ X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq377305 X1 (σ X0)
       have i₂ := eq365595 X0
       grind)
    | exact superpose eq365595 eq377305
    | (have j0 := eq377305 X1 (σ X0)
       grind)
    | exact resolve eq377305 eq365595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377305
  have eq1340323 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ X1) (M.op X0 X0)) ∨ (τ (k (σ X0) X1)) = (M.op (τ X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1339466 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1339466
    | (have j0 := eq1339466 X0 X1
       grind)
    | exact resolve eq1339466 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1339466
  have eq1340439 : ∀ X0 X1 : G, (M.op (τ X1) (M.op X0 X0)) = X0 ∨ (τ (k (σ X0) X1)) = (M.op (τ X1) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1340323 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1340323
    | (have j0 := eq1340323 X0 X1
       grind)
    | exact resolve eq1340323 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340323
  have eq1340505 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (M.op (τ X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1340439 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1340439
    | (have j0 := eq1340439 X0 X1
       grind)
    | exact resolve eq1340439 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340439
  have eq1340539 : ∀ X0 X1 : G, (M.op (τ X1) (M.op X0 X0)) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1340505 X0 X1
       have i₂ := eq29 X1 X0
       grind)
    | exact superpose eq29 eq1340505
    | (have j0 := eq1340505 X0 X1
       grind)
    | exact resolve eq1340505 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1340505
  have eq1340656 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1340539 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1340539
    | exact resolve eq1340539 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1340539
  have eq1344283 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq622 (M.op X1 X1) X0
       have i₂ := eq1340656 X0 X1
       grind)
    | exact superpose eq1340656 eq622
    | (have j1 := eq1340656 X0 X1
       grind)
    | exact resolve eq622 eq1340656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622 eq1340656
  have eq1345228 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0
       have i₂ := eq1344283 X0 X1
       grind)
    | (have i₁ := eq57 X0
       have i₂ := eq1344283 X0 X0
       grind)
    | exact superpose eq1344283 eq57
    | (have j1 := eq1344283 X0 X1
       grind)
    | exact resolve eq57 eq1344283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1348154 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X1 X0)) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq762 X0 X1 X2
       have i₂ := eq1345228 X0 X1
       grind)
    | exact superpose eq1345228 eq762
    | (have j1 := eq1345228 X0 X1
       grind)
    | exact resolve eq762 eq1345228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762 eq1345228
  have eq1363064 : ∀ X1 X2 : G, (τ X1) = (τ (M.op X1 (M.op X2 X1))) ∨ (M.op X1 X2) = (k X2 X1) := by
    intro X1 X2
    first
    | (have i₁ := eq423912 x X1 X2
       have i₂ := eq1348154 X1 X2 x
       grind)
    | exact superpose eq1348154 eq423912
    | (have j1 := eq1348154 X1 X2 X2
       grind)
    | exact resolve eq423912 eq1348154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423912 eq1348154
  have eq1365096 : ∀ X0 X1 : G, (M.op (τ X1) (τ X1)) = (τ (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1)))) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq365594 (M.op X1 (M.op x X1))
       have i₂ := eq1363064 X1 x
       grind)
    | exact superpose eq1363064 eq365594
    | (have j1 := eq1363064 X1 X0
       grind)
    | exact resolve eq365594 eq1363064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363064
  have eq1365199 : ∀ X0 X1 : G, (M.op (τ X1) (τ X1)) = (τ (M.op X1 (M.op X1 (M.op X0 X1)))) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1365096 X0 X1
       have i₂ := eq979 X1 X1 X0 X1 X0
       grind)
    | exact superpose eq979 eq1365096
    | (have j0 := eq1365096 X0 X1
       grind)
    | exact resolve eq1365096 eq979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979 eq1365096
  have eq1365579 : ∀ X0 X1 : G, (M.op (τ X1) (τ X1)) = (τ (M.op X0 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1365199 X0 X1
       have i₂ := eq2590 X1 X0
       grind)
    | exact superpose eq2590 eq1365199
    | (have j0 := eq1365199 X0 X1
       grind)
    | exact resolve eq1365199 eq2590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2590 eq1365199
  have eq1365696 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (τ (M.op X1 X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1365579 X0 X1
       have i₂ := eq365594 X1
       grind)
    | exact superpose eq365594 eq1365579
    | (have j0 := eq1365579 X0 X1
       grind)
    | exact resolve eq1365579 eq365594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365594 eq1365579
  have eq1367320 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (M.op (σ X1) (σ X1))) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1365696 (σ X0) (σ X1)
       have i₂ := eq377 X0 X1
       grind)
    | exact superpose eq377 eq1365696
    | (have j0 := eq1365696 (σ X0) (σ X1)
       have j1 := eq377 X0 X1
       grind)
    | exact resolve eq1365696 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq1365696
  have eq1368278 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (M.op X1 X1))) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1367320 X0 X1
       have i₂ := eq365595 X1
       grind)
    | exact superpose eq365595 eq1367320
    | (have j0 := eq1367320 X0 X1
       grind)
    | exact resolve eq1367320 eq365595
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365595 eq1367320
  have eq1368554 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1368278 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq1368278
    | (have j0 := eq1368278 X0 X1
       grind)
    | exact resolve eq1368278 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368278
  have eq1368637 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1368554 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1368554
    | (have j0 := eq1368554 X0 X1
       grind)
    | exact resolve eq1368554 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368554
  have eq1368678 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1368637 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1368637
    | (have j0 := eq1368637 X0 X1
       grind)
    | exact resolve eq1368637 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368637
  have eq1368679 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1368678 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368678
  have eq1370096 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1368679 y x
       grind)
    | exact superpose eq1368679 eq16
    | (have j1 := eq1368679 y x
       grind)
    | exact resolve eq16 eq1368679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368679
  have eq1371986 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ (M.op x x) = (M.op y x) := by
    first
    | (have i₁ := eq1370096
       have i₂ := eq1344283 x y
       grind)
    | exact superpose eq1344283 eq1370096
    | (have j1 := eq1344283 x y
       grind)
    | exact resolve eq1370096 eq1344283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344283
  have eq1371987 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1370096
       have i₂ := eq5160 x y
       grind)
    | exact superpose eq5160 eq1370096
    | (have j1 := eq5160 x y
       grind)
    | (have r₁ := eq1370096
       have r₂ := eq5160 x y
       grind)
    | exact resolve eq1370096 eq5160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5160 eq1370096
  have eq1371995 : y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq1371987
  have eq1371996 : (M.op x x) = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq1371986
  have eq1373416 : y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1371995
       have i₂ := eq1371996
       grind)
    | exact superpose eq1371996 eq1371995
    | exact resolve eq1371995 eq1371996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1371995 eq1371996
  have eq1373937 : y = (M.op x x) := by grind
  clear eq1373416
  have eq1374000 : x = (M.op x y) := by
    first
    | (have i₁ := eq57 x
       have i₂ := eq1373937
       grind)
    | exact superpose eq1373937 eq57
    | exact resolve eq57 eq1373937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq1374104 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq366090 x
       have i₂ := eq1373937
       grind)
    | exact superpose eq1373937 eq366090
    | exact resolve eq366090 eq1373937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366090 eq1373937
  have eq1382786 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1374104
       grind)
    | exact superpose eq1374104 eq16
    | exact resolve eq16 eq1374104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374104
  have eq1383503 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1382786
       have i₂ := eq1374000
       grind)
    | exact superpose eq1374000 eq1382786
    | exact resolve eq1382786 eq1374000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1374000 eq1382786
  have eq1383504 : False := by grind
  exact eq1383504

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pyx_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq51 : ∀ X0 : G, x = (M.op (M.op X0 (M.op x y)) (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X1 : G, (k (M.op X1 X1) X1) = X1 := by
    intro X1
    grind
  have eq68 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq69 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ x) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq73 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq73
    | exact resolve eq73 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq80
    | exact resolve eq80 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq82
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq82
    | exact resolve eq82 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq103 : y ≠ (M.op x y) ∨ x = (M.op y y) ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq91
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq16
    | exact resolve eq16 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq105
  have eq230 : ∀ X0 : G, (k (σ x) X0) = (σ (M.op x (τ X0))) ∨ (τ X0) = (M.op x (τ X0)) ∨ x = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq11 x (τ X0)
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x (τ X0)
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq246 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq27 eq56
    | (have j0 := eq56 (σ y) (σ x)
       grind)
    | exact resolve eq56 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq247 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (M.op X0 X0) X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq65 (M.op X0 X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq65
    | exact resolve eq65 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq272 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq411 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X0 X0) X0 X1 X2
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : ∀ X0 X1 : G, (M.op X0 (M.op y X1)) = (M.op (M.op x y) (M.op (M.op X0 (M.op y X1)) (M.op X0 (M.op y X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq53 y x X0 X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 y x X0 X1
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq421 : ∀ X0 X1 : G, (M.op X0 (M.op (σ y) X1)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (M.op (σ y) X1)) (M.op X0 (M.op (σ y) X1)))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ y) (σ x) X0 X1
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op X1 X0) X1 X2 (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))
       have i₂ := eq53 X0 X1 X2 X3
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq426 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op X1 (M.op X0 X2)) X1 X2 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X1 X2 : G, (M.op X0 x) = (M.op (M.op X2 (M.op X1 (M.op x y))) (M.op (M.op X0 x) (M.op X0 x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq51 eq53
    | exact resolve eq53 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq429 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op (M.op X2 (M.op X1 (M.op (σ x) (σ y)))) (M.op (M.op X0 (σ x)) (M.op X0 (σ x)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq445 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X2 (M.op X0 X1) X1
       have i₂ := eq56 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq56 eq53
    | exact resolve eq53 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq478 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq272 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq272
    | (have j0 := eq272 X0 y
       grind)
    | exact resolve eq272 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq558 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (M.op (σ X0) X2)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) X1 X2
       have i₂ := eq68 X0 X0
       grind)
    | exact superpose eq68 eq14
    | (have j1 := eq68 X0 X0
       grind)
    | exact resolve eq14 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq562 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq68 X0 X1
       grind)
    | exact superpose eq68 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq68 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq68 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq68 X0 X0
       grind)
    | exact resolve eq12 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq567 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq562 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq568 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (M.op (σ X0) X2)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq558 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558
  have eq574 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq567 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq567 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq567 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq567 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq583 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq574 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq574
    | (have j0 := eq574 X0 X1
       grind)
    | exact resolve eq574 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq597 : (k (k y y) y) = (τ (k (k (σ y) (σ y)) (σ y))) := by
    first
    | exact superpose eq110 eq478
    | exact resolve eq478 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq3326 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq423 X0 X0 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq423
    | exact resolve eq423 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq3505 : ∀ X0 X1 : G, (M.op x x) = (M.op (M.op X0 (M.op X1 (M.op x y))) x) := by
    intro X0 X1
    first
    | (have i₁ := eq428 x X1 X0
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq428
    | exact resolve eq428 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq3537 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq429 sF2 X1 x
       have i₂ := eq56 sF2 sF2
       grind)
    | exact superpose eq56 eq429
    | exact resolve eq429 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq3555 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3505 sF0 sF0
       have i₂ := eq54 sF0
       grind)
    | exact superpose eq54 eq3505
    | exact resolve eq3505 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3505
  have eq3799 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq3537 sF4 sF4
       have i₂ := eq54 sF4
       grind)
    | exact superpose eq54 eq3537
    | exact resolve eq3537 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3537
  have eq3821 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq3799 eq14
    | exact resolve eq14 eq3799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3838 : ∀ X0 : G, (M.op (M.op y X0) (M.op y X0)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq419 (M.op y X0) X0
       have i₂ := eq56 (M.op y X0) (M.op y X0)
       grind)
    | exact superpose eq56 eq419
    | exact resolve eq419 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq3860 : ∀ X0 : G, (M.op (M.op (σ y) X0) (M.op (σ y) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq421 (M.op sF3 x) x
       have i₂ := eq56 (M.op sF3 x) (M.op sF3 x)
       grind)
    | exact superpose eq56 eq421
    | exact resolve eq421 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421
  have eq3976 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq426 X0 X2 (M.op X0 X1) X1 (M.op X0 X1)
       have i₂ := eq54 (M.op X0 X1)
       grind)
    | exact superpose eq54 eq426
    | exact resolve eq426 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4029 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq426 X0 X0 X2 X3 X1
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq426
    | exact resolve eq426 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426
  have eq4234 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq3821 sF2
       have i₂ := eq54 sF2
       grind)
    | exact superpose eq54 eq3821
    | exact resolve eq3821 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3821
  have eq4819 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op (σ y) X1)) (σ (k y y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq568 y X0 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq568
    | (have j0 := eq568 y X0 X1
       grind)
    | exact resolve eq568 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq4866 : ∀ X0 X1 : G, (σ y) = (M.op (M.op X0 (M.op (σ y) X1)) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq4819 X0 X1
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq4819
    | exact resolve eq4819 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4819
  have eq4978 : ∀ X0 : G, (σ X0) ≠ (σ (k x X0)) ∨ (σ X0) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq69 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq5910 : ∀ X0 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq564 (M.op X0 X0) X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq564
    | (have j0 := eq564 (M.op X0 X0) X0
       grind)
    | exact resolve eq564 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6028 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq5910 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5910
  have eq6729 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq411 X0 X1 (M.op X0 X0)
       have i₂ := eq56 X0 X0
       grind)
    | exact superpose eq56 eq411
    | exact resolve eq411 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6777 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X2)) ≠ (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2))) ∨ (M.op (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2))) (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2)))) = X1 ∨ (M.op (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2))) (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2)))) = (k X1 (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2)))
       have i₂ := eq411 X1 X0 X2
       grind)
    | exact superpose eq411 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2)))
       grind)
    | exact resolve eq12 eq411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq6794 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X2)) = X1 ∨ (M.op X0 (M.op (M.op X1 X1) X2)) ≠ (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2))) ∨ (M.op (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2))) (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2)))) = (k X1 (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6777 X0 X1 X2
       have i₂ := eq56 (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2))
       grind)
    | exact superpose eq56 eq6777
    | (have j0 := eq6777 X0 X1 X2
       grind)
    | exact resolve eq6777 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6777
  have eq6797 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X1) X2)) ≠ (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2))) ∨ (M.op X0 (M.op (M.op X1 X1) X2)) = X1 ∨ (M.op X0 (M.op (M.op X1 X1) X2)) = (k X1 (M.op (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6794 X0 X1 X2
       have i₂ := eq56 (M.op X0 (M.op (M.op X1 X1) X2)) (M.op X0 (M.op (M.op X1 X1) X2))
       grind)
    | exact superpose eq56 eq6794
    | (have j0 := eq6794 X0 X1 X2
       grind)
    | exact resolve eq6794 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6794
  have eq8009 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    by_contra hcon
    push Not at hcon
    have f8009_12 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
      intro X0 X1 X2 X3 X4 X5
      grind
    have f8009_13 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
      intro X0
      grind
    have f8009_19 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
      intro X0 X1 X2
      grind
    have f8009_22 : (M.op X0 X1) ≠ (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op X0 X1) (M.op X0 X1))) := by grind
    have f8009_26 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f8009_19 X0 X1 (M.op X0 X0)
         have i₂ := f8009_13 X0
         grind)
      | exact superpose f8009_13 f8009_19
      | exact resolve f8009_19 f8009_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8009_27 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
      intro X0 X1 X2 X3
      first
      | (have i₁ := f8009_19 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
         have i₂ := f8009_19 X0 X2 X3
         grind)
      | exact superpose f8009_19 f8009_19
      | exact resolve f8009_19 f8009_19
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8009_35 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
      intro X0 X1 X2
      first
      | (have i₁ := f8009_19 (M.op X0 X0) X1 X2
         have i₂ := f8009_26 X0 X0
         grind)
      | exact superpose f8009_26 f8009_19
      | exact resolve f8009_19 f8009_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8009_92 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X3 (M.op X4 X0)) (M.op (M.op X1 (M.op X2 X0)) (M.op X1 (M.op X2 X0)))) := by
      intro X0 X1 X2 X3 X4
      first
      | (have i₁ := f8009_12 X0 X0 (M.op X0 X0) X3 X4 x
         have i₂ := f8009_13 X0
         grind)
      | exact superpose f8009_13 f8009_12
      | exact resolve f8009_12 f8009_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8009_110 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) = (M.op (M.op X3 (M.op X4 X1)) (M.op X0 (M.op X1 X2))) := by
      intro X0 X1 X2 X3 X4
      first
      | (have i₁ := f8009_12 X0 X1 X2 (M.op X0 (M.op X1 X2)) X4 X3
         have i₂ := f8009_26 (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))
         grind)
      | exact superpose f8009_26 f8009_12
      | exact resolve f8009_12 f8009_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8009_501 : ∀ X0 X2 X3 : G, (M.op (M.op X2 (M.op X3 X0)) (M.op X0 X0)) = X0 := by
      intro X0 X2 X3
      first
      | (have i₁ := f8009_92 X0 (M.op x X0) X0 X3 x
         have i₂ := f8009_26 X0 x
         grind)
      | exact superpose f8009_26 f8009_92
      | exact resolve f8009_92 f8009_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8009_796 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
      intro X0 X1 X2 X3
      first
      | (have i₁ := f8009_35 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
         have i₂ := f8009_27 X1 X1 X0 X2
         grind)
      | exact superpose f8009_27 f8009_35
      | exact resolve f8009_35 f8009_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8009_1430 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
      intro X0 X1
      first
      | (have i₁ := f8009_796 (M.op X0 X1) X0 X1 (M.op x (M.op x (M.op X0 X1)))
         have i₂ := f8009_501 (M.op X0 X1) x x
         grind)
      | exact superpose f8009_501 f8009_796
      | exact resolve f8009_796 f8009_501
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8009_1527 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
      intro X0 X1
      first
      | (have i₁ := f8009_1430 (M.op X1 X0) (M.op X0 X0)
         have i₂ := f8009_26 X0 X1
         grind)
      | exact superpose f8009_26 f8009_1430
      | exact resolve f8009_1430 f8009_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8009_2965 : (M.op X0 X1) ≠ (M.op (M.op X2 (M.op X3 X0)) (M.op X1 (M.op X0 X1))) := by
      first
      | (have i₁ := f8009_22
         have i₂ := f8009_1527 X1 X0
         grind)
      | exact superpose f8009_1527 f8009_22
      | exact resolve f8009_22 f8009_1527
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8009_3002 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 (M.op X1 X0)) (M.op X0 (M.op X1 X0))) := by
      intro X0 X1 X2
      first
      | (have i₁ := f8009_26 (M.op X1 X0) X2
         have i₂ := f8009_1527 X0 X1
         grind)
      | exact superpose f8009_1527 f8009_26
      | exact resolve f8009_26 f8009_1527
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8009_3056 : (M.op X0 X1) ≠ (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (M.op X0 X1))) := by
      first
      | (have i₁ := f8009_2965
         have i₂ := f8009_110 X1 X0 X1 X2 X3
         grind)
      | exact superpose f8009_110 f8009_2965
      | exact resolve f8009_2965 f8009_110
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f8009_3068 : False := by
      first
      | (have r₁ := f8009_3056
         have r₂ := f8009_3002 X1 X0 X1
         grind)
      | exact resolve f8009_3056 f8009_3002
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f8009_3068
  clear eq425
  have eq12182 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq83 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12183 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12182
    | exact resolve eq12182 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12182
  have eq12194 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq12183
       have r₂ := eq28
       grind)
    | exact resolve eq12183 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12183
  have eq12196 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq12194
    | exact resolve eq12194 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12194
  have eq12206 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12196 eq65
    | exact resolve eq65 eq12196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12196
  have eq14233 : (τ (σ y)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq12206 eq60
    | exact resolve eq60 eq12206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq12206
  have eq14259 : y = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq14233
    | exact resolve eq14233 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14233
  have eq15018 : y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq14259
       grind)
    | exact superpose eq14259 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq14259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14259
  have eq15019 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15018
  have eq15023 : y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15019
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq15019
    | exact resolve eq15019 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15019
  have eq15024 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15023
  have eq15075 : y = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq65 y
       have i₂ := eq15024
       grind)
    | exact superpose eq15024 eq65
    | exact resolve eq65 eq15024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15076 : ∀ X0 : G, x = (M.op (M.op X0 x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq247 y x
       have i₂ := eq15024
       grind)
    | exact superpose eq15024 eq247
    | exact resolve eq247 eq15024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15024
  have eq15154 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq564 x y
       have i₂ := eq15075
       grind)
    | exact superpose eq15075 eq564
    | (have j0 := eq564 x y
       grind)
    | exact resolve eq564 eq15075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564 eq15075
  have eq15157 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq15154
  have eq15160 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15157
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15157
    | exact resolve eq15157 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15157
  have eq15172 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15160
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15160
    | exact resolve eq15160 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15160
  have eq15177 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq15172
    | exact resolve eq15172 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15172
  have eq15178 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq15177
  have eq15183 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15178
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq15178
    | exact resolve eq15178 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15178
  have eq15188 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq15183
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq15183
    | exact resolve eq15183 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15183
  have eq15332 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq15188 eq247
    | exact resolve eq247 eq15188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247 eq15188
  have eq16080 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3326 y (M.op x x)
       have i₂ := eq15076 x
       grind)
    | exact superpose eq15076 eq3326
    | exact resolve eq3326 eq15076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15076
  have eq16090 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16080
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16080
    | exact resolve eq16080 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16080
  have eq16094 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq111
       have i₂ := eq16090
       grind)
    | exact superpose eq16090 eq111
    | exact resolve eq111 eq16090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq16090
  have eq16132 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq16094
  have eq16142 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq16132
    | exact resolve eq16132 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16132
  have eq18523 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15332 eq3326
    | exact resolve eq3326 eq15332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15332
  have eq18540 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq18523
    | exact resolve eq18523 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18523
  have eq18675 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18540 eq246
    | exact resolve eq246 eq18540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20651 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4029 X0 (M.op X0 X1) (M.op X0 X1) X1
       have i₂ := eq54 (M.op X0 X1)
       grind)
    | exact superpose eq54 eq4029
    | exact resolve eq4029 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26596 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6729 X2 X1
       have i₂ := eq445 X1 X2 X0
       grind)
    | (have i₁ := eq6729 X1 X1
       have i₂ := eq445 X1 X1 X1
       grind)
    | exact superpose eq445 eq6729
    | exact resolve eq6729 eq445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq445 eq6729
  have eq28977 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18540 eq3976
    | (have j0 := eq3976 (σ y) X0 (σ x)
       grind)
    | exact resolve eq3976 eq18540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31575 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ y))) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18540 eq4866
    | exact resolve eq4866 eq18540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4866 eq18540
  have eq31637 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ y))) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq31575 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31575
  have eq37283 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq18675 eq28977
    | exact resolve eq28977 eq18675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28977
  have eq37334 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq37283 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37283
  have eq38411 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq16142 eq31637
    | exact resolve eq31637 eq16142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16142 eq31637
  have eq38442 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ y))) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq38411 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38411
  have eq38469 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18675 eq38442
    | exact resolve eq38442 eq18675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18675
  have eq38476 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38442 eq56
    | exact resolve eq56 eq38442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38488 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38442 eq3326
    | exact resolve eq3326 eq38442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3326 eq38442
  have eq38496 : (σ y) = (M.op (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq38469
  have eq39654 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38476 eq37334
    | exact resolve eq37334 eq38476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37334 eq38476
  have eq39689 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq39654
  have eq40060 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq38488 eq38496
    | exact resolve eq38496 eq38488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38488 eq38496
  have eq40101 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq40060
  have eq40373 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40101 eq54
    | exact resolve eq54 eq40101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq40101
  have eq40411 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40373 eq39689
    | exact resolve eq39689 eq40373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39689 eq40373
  have eq40460 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq40411
  have eq40465 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq40460
       have r₂ := eq28
       grind)
    | exact resolve eq40460 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40460
  have eq40730 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40465 eq28
    | exact resolve eq28 eq40465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40743 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40465 eq3799
    | exact resolve eq3799 eq40465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3799
  have eq40748 : (σ y) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40465 eq4234
    | exact resolve eq4234 eq40465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4234
  have eq41032 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40743 eq3860
    | exact resolve eq3860 eq40743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40743
  have eq41109 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq41032
       have i₂ := eq56 sF2 sF2
       grind)
    | exact superpose eq56 eq41032
    | exact resolve eq41032 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41032
  have eq41400 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (M.op (σ y) X0) (M.op (σ y) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq40748 eq8009
    | exact resolve eq8009 eq40748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8009
  have eq41439 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3860 eq41400
    | exact resolve eq41400 eq3860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3860 eq41400
  have eq41442 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40465 eq41109
    | exact resolve eq41109 eq40465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41109
  have eq41500 : (σ x) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ y = (M.op x y) := by grind
  clear eq41442
  have eq47556 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op (M.op (σ y) X0) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq41439 eq4029
    | exact resolve eq4029 eq41439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4029 eq41439
  have eq47784 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq41500 eq47556
    | exact resolve eq47556 eq41500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41500 eq47556
  have eq47921 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq47784
  have eq47929 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq47921
    | exact resolve eq47921 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47921
  have eq48197 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq47929 eq246
    | exact resolve eq246 eq47929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246
  have eq48213 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq47929 eq40748
    | exact resolve eq40748 eq47929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40748
  have eq48247 : (σ y) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq47929 eq65
    | exact resolve eq65 eq47929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq48249 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq47929 eq249
    | exact resolve eq249 eq47929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq48303 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq48213
  have eq48331 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40465 eq48197
    | exact resolve eq48197 eq40465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48197
  have eq48431 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq48331
  have eq48806 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq40465 eq48247
    | exact resolve eq48247 eq40465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40465 eq48247
  have eq48828 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq48806
  have eq50150 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq48828 eq110
    | exact resolve eq110 eq48828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50154 : (τ (k (σ y) (σ y))) = (k (k y y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq48828 eq597
    | exact resolve eq597 eq48828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597
  have eq50226 : (k y y) = (k (k y y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq110 eq50154
    | exact resolve eq50154 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50154
  have eq50230 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq50150
    | exact resolve eq50150 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq50150
  have eq50535 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq50230
       grind)
    | exact superpose eq50230 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq50230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50536 : y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq50535
  have eq50933 : ∀ X0 : G, y = (M.op (M.op y X0) (M.op y y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3976 y x y
       have i₂ := eq50536
       grind)
    | exact superpose eq50536 eq3976
    | exact resolve eq3976 eq50536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3976
  have eq65124 : (σ y) ≠ (σ (k y y)) ∨ (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ (k y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq583 (k y y) y
       have i₂ := eq50226
       grind)
    | exact superpose eq50226 eq583
    | (have j0 := eq583 y y
       grind)
    | exact resolve eq583 eq50226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq50226
  have eq65127 : (σ y) ≠ (σ (k y y)) ∨ (σ (k y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq65124
  have eq65135 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ (k y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq65127
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq65127
    | exact resolve eq65127 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65127
  have eq65140 : (σ y) ≠ (k (σ y) (σ y)) ∨ (σ (k y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq65135
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq65135
    | exact resolve eq65135 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65135
  have eq65144 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq65140
       have r₂ := eq48828
       grind)
    | exact resolve eq65140 eq48828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48828 eq65140
  have eq65147 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq65144
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq65144
    | exact resolve eq65144 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65144
  have eq65150 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq65147
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq65147
    | exact resolve eq65147 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq65147
  have eq65442 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq65150 eq110
    | exact resolve eq110 eq65150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq65150
  have eq66124 : (τ (M.op (σ x) (σ y))) = (k y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq47929 eq65442
    | exact resolve eq65442 eq47929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47929 eq65442
  have eq66254 : (τ (M.op (σ x) (σ y))) = (k y y) ∨ y = (M.op x y) := by grind
  clear eq66124
  have eq66583 : y = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq50230
       have i₂ := eq66254
       grind)
    | exact superpose eq66254 eq50230
    | exact resolve eq50230 eq66254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50230 eq66254
  have eq66605 : y = (τ (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq66583
  have eq75739 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq50933 X0
       have i₂ := eq50536
       grind)
    | exact superpose eq50536 eq50933
    | exact resolve eq50933 eq50536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50536 eq50933
  have eq75827 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq75739 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75739
  have eq188888 : (σ (M.op x y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq66605 eq230
    | exact resolve eq230 eq66605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230 eq66605
  have eq189024 : (σ (M.op x y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq188888
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq188888
    | exact resolve eq188888 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188888
  have eq189032 : (σ (M.op x y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq189024
    | exact resolve eq189024 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189024
  have eq189039 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq189032
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq189032
    | exact resolve eq189032 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189032
  have eq189040 : (σ (M.op x y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq189039
  have eq1710313 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq48303 eq26596
    | exact resolve eq26596 eq48303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26596 eq48303
  have eq1712204 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ x) (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1710313 eq6797
    | exact resolve eq6797 eq1710313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6797 eq1710313
  have eq1712488 : (σ y) = (k (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1712204
       have r₂ := eq48431
       grind)
    | exact resolve eq1712204 eq48431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1712204
  have eq1734753 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq48431 eq1712488
    | exact resolve eq1712488 eq48431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48431 eq1712488
  have eq1734844 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1734753
  have eq1734878 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1734844 eq83
    | exact resolve eq83 eq1734844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq1734844
  have eq1734969 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (σ y) := by grind
  clear eq1734878
  have eq1734983 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1734969
       have r₂ := eq40730
       grind)
    | exact resolve eq1734969 eq40730
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40730 eq1734969
  have eq1735175 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq75827 y
       have i₂ := eq1734983
       grind)
    | exact superpose eq1734983 eq75827
    | exact resolve eq75827 eq1734983
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1734983
  have eq1735376 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq1735175
  have eq1735439 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1735376
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1735376
    | exact resolve eq1735376 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1735376
  have eq1735440 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1735439
  have eq1735843 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1735440 eq48249
    | exact resolve eq48249 eq1735440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48249 eq1735440
  have eq1738653 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq1735843
  have eq1747970 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1738653 eq189040
    | exact resolve eq189040 eq1738653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189040 eq1738653
  have eq1748073 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq1747970
  have eq1748092 : x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1748073
       have r₂ := eq28
       grind)
    | exact resolve eq1748073 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1748073
  have eq1764897 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq75827 y
       have i₂ := eq1748092
       grind)
    | exact superpose eq1748092 eq75827
    | exact resolve eq75827 eq1748092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75827 eq1748092
  have eq1765102 : y = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq1764897
  have eq1765203 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1765102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1765102
    | exact resolve eq1765102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1765102
  have eq1765204 : y = (M.op x y) := by grind
  clear eq1765203
  have eq1765237 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1765204 eq21
    | exact resolve eq21 eq1765204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq1765244 : y ≠ y ∨ x = (M.op y y) ∨ (k x y) = (M.op y y) := by
    first
    | exact superpose eq1765204 eq103
    | (have r₁ := eq103
       have r₂ := eq1765204
       grind)
    | exact resolve eq103 eq1765204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq1765409 : (M.op x x) = (M.op y x) := by
    first
    | exact superpose eq1765204 eq3555
    | exact resolve eq3555 eq1765204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3555
  have eq1765550 : x = (M.op y y) ∨ (k x y) = (M.op y y) := by grind
  clear eq1765244
  have eq1765751 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1765237
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1765237
    | exact resolve eq1765237 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1765237
  have eq1765764 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1765751 eq27
    | exact resolve eq27 eq1765751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1768572 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq3838 x
       have i₂ := eq1765409
       grind)
    | exact superpose eq1765409 eq3838
    | exact resolve eq3838 eq1765409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3838 eq1765409
  have eq1768771 : (M.op (M.op x x) (M.op x x)) = (M.op y (M.op x x)) := by
    first
    | exact superpose eq1765204 eq1768572
    | exact resolve eq1768572 eq1765204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1768572
  have eq1768793 : x = (M.op y (M.op x x)) := by
    first
    | (have i₁ := eq1768771
       have i₂ := eq56 x x
       grind)
    | exact superpose eq56 eq1768771
    | exact resolve eq1768771 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq1768771
  have eq1770097 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq20651 y (M.op x x)
       have i₂ := eq1768793
       grind)
    | exact superpose eq1768793 eq20651
    | exact resolve eq20651 eq1768793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20651 eq1768793
  have eq1770117 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1770097
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1770097
    | exact resolve eq1770097 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1770097
  have eq1770187 : y = (M.op y y) := by
    first
    | exact superpose eq1765204 eq1770117
    | exact resolve eq1770117 eq1765204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1765204 eq1770117
  have eq1770371 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6028 y
       have i₂ := eq1770187
       grind)
    | exact superpose eq1770187 eq6028
    | exact resolve eq6028 eq1770187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6028
  have eq1770456 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1770371
  have eq1770512 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1770456
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1770456
    | exact resolve eq1770456 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770456
  have eq1770555 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1765751 eq1770512
    | exact resolve eq1770512 eq1765751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770512
  have eq2022165 : x = y ∨ (k x y) = (M.op y y) := by
    first
    | (have i₁ := eq1765550
       have i₂ := eq1770187
       grind)
    | exact superpose eq1770187 eq1765550
    | exact resolve eq1765550 eq1770187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1765550
  have eq2022166 : y = (k x y) ∨ x = y := by
    first
    | (have i₁ := eq2022165
       have i₂ := eq1770187
       grind)
    | exact superpose eq1770187 eq2022165
    | exact resolve eq2022165 eq1770187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770187 eq2022165
  have eq2022231 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq4978 y
       have i₂ := eq2022166
       grind)
    | exact superpose eq2022166 eq4978
    | (have j0 := eq4978 y
       grind)
    | exact resolve eq4978 eq2022166
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4978 eq2022166
  have eq2022308 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq2022231
  have eq2022378 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2022308
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2022308
    | exact resolve eq2022308 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022308
  have eq2022496 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq2022378
    | exact resolve eq2022378 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2022378
  have eq2022606 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1765751 eq2022496
    | exact resolve eq2022496 eq1765751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022496
  have eq2022711 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq2022606
       have r₂ := eq28
       grind)
    | exact resolve eq2022606 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022606
  have eq2022799 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2022711
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq2022711
    | exact resolve eq2022711 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022711
  have eq2022874 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq1765751 eq2022799
    | exact resolve eq2022799 eq1765751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022799
  have eq2022945 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq1770555 eq2022874
    | exact resolve eq2022874 eq1770555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022874
  have eq2023959 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq2022945 eq1765764
    | exact resolve eq1765764 eq2022945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022945
  have eq2023983 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1770555 eq2023959
    | exact resolve eq2023959 eq1770555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2023959
  have eq2024144 : x = y := by
    first
    | (have r₁ := eq2023983
       have r₂ := eq28
       grind)
    | exact resolve eq2023983 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2023983
  have eq2024474 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq2024144
       grind)
    | exact superpose eq2024144 eq25
    | exact resolve eq25 eq2024144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2024144
  have eq2026019 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1765751 eq2024474
    | exact resolve eq2024474 eq1765751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1765751 eq2024474
  have eq2026601 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2026019
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2026019
    | exact resolve eq2026019 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2026019
  have eq2027814 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2026601 eq1765764
    | exact resolve eq1765764 eq2026601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1765764 eq2026601
  have eq2027839 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1770555 eq2027814
    | exact resolve eq2027814 eq1770555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1770555 eq2027814
  have eq2028000 : False := by grind
  exact eq2028000

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pyy_y_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq49 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : y ≠ (M.op x y) ∨ x = (M.op y y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq74 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq81 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq74
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq75
    | exact resolve eq75 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq83
    | exact resolve eq83 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq85
    | exact resolve eq85 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq275 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq424 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq49 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq49
    | exact resolve eq49 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq469 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq275 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq275
    | (have j0 := eq275 X0 y
       grind)
    | exact resolve eq275 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq21 eq275
    | (have j0 := eq275 X0 (M.op x y)
       grind)
    | exact resolve eq275 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq565 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq71 X0 X0
       grind)
    | exact superpose eq71 eq50
    | (have j1 := eq71 X0 X0
       grind)
    | exact resolve eq50 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq573 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq579 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq565 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq3384 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq424 X0 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq424
    | exact resolve eq424 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq3410 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq3384 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3384
    | (have j0 := eq3384 y x
       grind)
    | exact resolve eq3384 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3412 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3384
    | (have j0 := eq3384 (σ y) (σ x)
       grind)
    | exact resolve eq3384 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3725 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k X0 (σ (τ X0)))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq579 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq579
    | (have j0 := eq579 (τ X0)
       grind)
    | exact resolve eq579 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq579
  have eq3744 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq3725 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3725
    | (have j0 := eq3725 X0
       grind)
    | exact resolve eq3725 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3725
  have eq3756 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3744 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3744
    | (have j0 := eq3744 X0
       grind)
    | exact resolve eq3744 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3744
  have eq6260 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq573 x y
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq573
    | (have j0 := eq573 x y
       grind)
    | exact resolve eq573 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq6327 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6260
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6260
    | exact resolve eq6260 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6260
  have eq6414 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6327
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6327
    | exact resolve eq6327 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6327
  have eq6499 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6414
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6414
    | exact resolve eq6414 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6414
  have eq6582 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq6499
    | exact resolve eq6499 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6499
  have eq6663 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) ≠ (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq6582
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq6582
    | exact resolve eq6582 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6582
  have eq6716 : (σ y) ≠ (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6663
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq6663
    | exact resolve eq6663 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6663
  have eq11791 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq86 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11792 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq11791
    | exact resolve eq11791 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11791
  have eq11803 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq11792
       have r₂ := eq28
       grind)
    | exact resolve eq11792 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11792
  have eq11805 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq11803
    | exact resolve eq11803 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11803
  have eq11813 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq11805
  have eq13690 : (τ (σ x)) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq11813 eq60
    | exact resolve eq60 eq11813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq11813
  have eq13711 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq13690
    | exact resolve eq13690 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13690
  have eq14230 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq13711
       grind)
    | exact superpose eq13711 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq13711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13711
  have eq14231 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq14230
  have eq14233 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14231
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14231
    | exact resolve eq14231 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14231
  have eq14244 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq14233
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14233
    | exact resolve eq14233 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14233
  have eq14245 : x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq14244
  have eq14289 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3384 y y
       have i₂ := eq14245
       grind)
    | exact superpose eq14245 eq3384
    | exact resolve eq3384 eq14245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14245
  have eq14290 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq14289
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14289
    | exact resolve eq14289 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14289
  have eq14291 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq14290
  have eq14297 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14291 eq28
    | exact resolve eq28 eq14291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14299 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14291 eq64
    | (have r₁ := eq64
       have r₂ := eq14291
       grind)
    | exact resolve eq64 eq14291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq14291
  have eq14317 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq14299
  have eq17962 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq14317 eq86
    | exact resolve eq86 eq14317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14317
  have eq17982 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17962
  have eq17995 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq17982
       have r₂ := eq14297
       grind)
    | exact resolve eq17982 eq14297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14297 eq17982
  have eq18379 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17995 eq3384
    | exact resolve eq3384 eq17995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17995
  have eq18386 : x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq18379
    | exact resolve eq18379 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18379
  have eq18426 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3384 y y
       have i₂ := eq18386
       grind)
    | exact superpose eq18386 eq3384
    | exact resolve eq3384 eq18386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18386
  have eq18432 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18426
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq18426
    | exact resolve eq18426 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18426
  have eq18433 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18432
  have eq18443 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18433 eq28
    | exact resolve eq28 eq18433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18453 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18433 eq3412
    | exact resolve eq3412 eq18433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3412
  have eq18475 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq18453
    | exact resolve eq18453 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18453
  have eq19101 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq18475
  have eq19418 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq18433 eq19101
    | exact resolve eq19101 eq18433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18433 eq19101
  have eq19437 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq19418
  have eq20708 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19437 eq86
    | exact resolve eq86 eq19437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq19437
  have eq20725 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq20708
  have eq20739 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20725
       have r₂ := eq18443
       grind)
    | exact resolve eq20725 eq18443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18443 eq20725
  have eq21311 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3384 y y
       have i₂ := eq20739
       grind)
    | exact superpose eq20739 eq3384
    | exact resolve eq3384 eq20739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20739
  have eq21319 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21311
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq21311
    | exact resolve eq21311 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21311
  have eq21320 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq21319
  have eq21331 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21320 eq21
    | exact resolve eq21 eq21320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21334 : y ≠ y ∨ x = (M.op y y) ∨ y = (k x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21320 eq63
    | (have r₁ := eq63
       have r₂ := eq21320
       grind)
    | exact resolve eq63 eq21320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq21392 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21320 eq470
    | exact resolve eq470 eq21320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470 eq21320
  have eq21411 : y = (k x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq21334
  have eq21418 : ∀ X0 : G, (τ (k X0 (σ y))) = (τ (k X0 (σ (M.op x y)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq21392 X0
       have i₂ := eq469 X0
       grind)
    | exact superpose eq469 eq21392
    | exact resolve eq21392 eq469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469 eq21392
  have eq21471 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21331
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq21331
    | exact resolve eq21331 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21331
  have eq21758 : (σ (M.op x y)) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21471 eq6716
    | exact resolve eq6716 eq21471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6716
  have eq21840 : (σ (M.op x y)) ≠ (k (σ x) (σ (M.op x y))) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq21758
       have r₂ := eq28
       grind)
    | exact resolve eq21758 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21758
  have eq28588 : ∀ X0 : G, (k X0 (σ y)) = (σ (τ (k X0 (σ (M.op x y))))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq21418 eq15
    | exact resolve eq15 eq21418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21418
  have eq28704 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq28588 X0
       have i₂ := eq15 (k X0 sF1)
       grind)
    | exact superpose eq15 eq28588
    | exact resolve eq28588 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28588
  have eq40874 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq21411
       grind)
    | exact superpose eq21411 eq45
    | exact resolve eq45 eq21411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21411
  have eq40909 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40874
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq40874
    | exact resolve eq40874 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40874
  have eq42256 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21471 eq40909
    | exact resolve eq40909 eq21471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42285 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq40909 eq28704
    | exact resolve eq28704 eq40909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28704 eq40909
  have eq42295 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq42285
  have eq42311 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq42256
  have eq45095 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq42295 eq21840
    | exact resolve eq21840 eq42295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21840 eq42295
  have eq45102 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq45095
  have eq45104 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq45102
       have r₂ := eq21471
       grind)
    | exact resolve eq45102 eq21471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21471 eq45102
  have eq46831 : (σ x) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq45104
  have eq47939 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq46831 eq42311
    | exact resolve eq42311 eq46831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42311 eq46831
  have eq47946 : x = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq47939
  have eq48007 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3384 y y
       have i₂ := eq47946
       grind)
    | exact superpose eq47946 eq3384
    | exact resolve eq3384 eq47946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47946
  have eq48029 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq48007
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq48007
    | exact resolve eq48007 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48007
  have eq48030 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq48029
  have eq48362 : x = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq48030 eq29
    | exact resolve eq29 eq48030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq48030
  have eq48598 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq48362
    | exact resolve eq48362 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq48362
  have eq48599 : x = (M.op x y) := by grind
  clear eq48598
  have eq48602 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq48599 eq21
    | exact resolve eq21 eq48599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq48687 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq48599 eq3410
    | exact resolve eq3410 eq48599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3410
  have eq48715 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq48687
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq48687
    | exact resolve eq48687 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq48687
  have eq48788 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq48602
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq48602
    | exact resolve eq48602 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48602
  have eq48789 : x = (M.op y y) := by
    first
    | exact superpose eq48599 eq48715
    | exact resolve eq48715 eq48599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48599 eq48715
  have eq48790 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq48788 eq27
    | exact resolve eq27 eq48788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq49046 : x = (k x y) := by grind
  have eq49059 : y = (M.op x x) := by
    first
    | (have i₁ := eq52 y y
       have i₂ := eq48789
       grind)
    | exact superpose eq48789 eq52
    | exact resolve eq52 eq48789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq48789
  have eq49130 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq49046
       grind)
    | exact superpose eq49046 eq45
    | exact resolve eq45 eq49046
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq49046
  have eq49155 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq48788 eq49130
    | exact resolve eq49130 eq48788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49130
  have eq49166 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq49155
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq49155
    | exact resolve eq49155 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49155
  have eq49175 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq48788 eq49166
    | exact resolve eq49166 eq48788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49166
  have eq49303 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq81
       have i₂ := eq49059
       grind)
    | exact superpose eq49059 eq81
    | exact resolve eq81 eq49059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq49059
  have eq49365 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq48788 eq49303
    | exact resolve eq49303 eq48788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49303
  have eq49372 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq49365
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq49365
    | exact resolve eq49365 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49365
  have eq49403 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq49175 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq11 eq49175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49175
  have eq49405 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq48790 eq49403
    | exact resolve eq49403 eq48790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49403
  have eq49417 : (σ y) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq49405
       have r₂ := eq28
       grind)
    | exact resolve eq49405 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49405
  have eq49428 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq48790 eq49417
    | exact resolve eq49417 eq48790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49417
  have eq52073 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq49372 eq3756
    | (have j0 := eq3756 (σ (M.op x y))
       grind)
    | exact resolve eq3756 eq49372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3756
  have eq52090 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq48790 eq52073
    | exact resolve eq52073 eq48790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52073
  have eq52101 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq52090
       have r₂ := eq28
       grind)
    | exact resolve eq52090 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52090
  have eq52947 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq49428 eq3384
    | exact resolve eq3384 eq49428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3384 eq49428
  have eq52960 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq48790 eq52947
    | exact resolve eq52947 eq48790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48790 eq52947
  have eq52965 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq52960
       have r₂ := eq28
       grind)
    | exact resolve eq52960 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52960
  have eq52968 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq52965 eq28
    | exact resolve eq28 eq52965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq52965
  have eq53864 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq52101
  have eq54648 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq53864 eq49372
    | exact resolve eq49372 eq53864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49372 eq53864
  have eq54674 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq54648
  have eq54682 : x = y := by
    first
    | (have r₁ := eq54674
       have r₂ := eq52968
       grind)
    | exact resolve eq54674 eq52968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54674
  have eq54714 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq54682
       grind)
    | exact superpose eq54682 eq25
    | exact resolve eq25 eq54682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq54682
  have eq54979 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq54714
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq54714
    | exact resolve eq54714 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq54714
  have eq55065 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq48788 eq54979
    | exact resolve eq54979 eq48788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48788 eq54979
  have eq55122 : False := by grind
  exact eq55122

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(Y,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxx_x_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq16 X0 X2 X3
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq16 X0 x x
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 (M.op X0 X0)
       have i₂ := eq177 X0
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | (have i₁ := eq180 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq180
    | (have j0 := eq180 y x
       grind)
    | exact resolve eq180 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq26 eq180
    | (have j0 := eq180 (σ y) (σ x)
       grind)
    | exact resolve eq180 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq180 X0 X0
       grind)
    | exact superpose eq180 eq13
    | (have j0 := eq13 X1 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq180 X0 X0
       grind)
    | (have r₁ := eq13 (M.op (M.op X1 (M.op X1 X1)) (M.op (M.op X1 X1) (M.op X1 X1))) X1
       have r₂ := eq180 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 X0) X1 X2
       have i₂ := eq180 X0 X0
       grind)
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq195 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq584 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq583 (M.op X0 X0)
       have i₂ := eq180 X0 X0
       grind)
    | exact superpose eq180 eq583
    | exact resolve eq583 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq177 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq177
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq177 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq663 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq583 x
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq583
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq583 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583
  have eq682 : (M.op x y) = (k x y) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq689 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
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
  have eq693 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq191
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq191
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq191 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq697 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq698 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq697 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq701 : (σ y) = (M.op (M.op (σ x) (σ y)) (k (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq693
  have eq711 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq663 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq715 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq659 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq659
  have eq716 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq658 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq1015 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 (k X0 X0)
       have i₂ := eq715 X0
       grind)
    | exact superpose eq715 eq11
    | (have j0 := eq11 X0 (k X0 X0)
       have j1 := eq715 X0
       grind)
    | exact resolve eq11 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq1021 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 ∨ (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1015 X0
       have j1 := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq1015 X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq1015 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq1015 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq1023 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq711 eq1021
    | (have j0 := eq1021 X0
       have j1 := eq711 X0
       grind)
    | exact resolve eq1021 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq1021
  have eq1025 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1023 X0
       have j1 := eq698 X0
       grind)
    | (have r₁ := eq1023 X0
       have r₂ := eq698 X0
       grind)
    | exact resolve eq1023 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq1023
  have eq1104 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (k (M.op X0 X0) X0)) (k (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 X0) X1 (M.op X0 X0)
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1108 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1104 X0 X1
       have i₂ := eq584 X0
       grind)
    | exact superpose eq584 eq1104
    | exact resolve eq1104 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1104
  have eq1137 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1108 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1108
    | (have j0 := eq1108 y x
       grind)
    | exact resolve eq1108 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1172 : y = (M.op (M.op x y) (M.op (M.op x y) y)) := by
    first
    | (have i₁ := eq190
       have i₂ := eq1137
       grind)
    | exact superpose eq1137 eq190
    | exact resolve eq190 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq1174 : ∀ X0 : G, (M.op (M.op x y) y) ≠ X0 ∨ (M.op X0 X0) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1137
       grind)
    | exact superpose eq1137 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 (M.op (M.op x y) y) y
       have r₂ := eq1137
       grind)
    | exact resolve eq13 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1178 : ∀ X0 : G, y = (M.op (M.op X0 y) (M.op (M.op x y) y)) := by
    intro X0
    first
    | (have i₁ := eq180 y X0
       have i₂ := eq1137
       grind)
    | exact superpose eq1137 eq180
    | exact resolve eq180 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1184 : (k y y) = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq1137
       grind)
    | exact superpose eq1137 eq11
    | exact resolve eq11 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1188 : (k y y) = (M.op (M.op x y) y) ∨ y = (M.op (M.op x y) y) := by grind
  clear eq1184
  have eq1462 : y = (M.op (M.op x y) (k y y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1188 eq1172
    | exact resolve eq1172 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq1472 : y = (M.op (k y y) (k y y)) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1188 eq1178
    | exact resolve eq1178 eq1188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178 eq1188
  have eq1497 : (k y y) = (M.op y (M.op (k y y) (k y y))) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1462 eq180
    | exact resolve eq180 eq1462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1462
  have eq1499 : (k y y) = (M.op y y) ∨ y = (M.op (M.op x y) y) := by
    first
    | exact superpose eq1472 eq1497
    | exact resolve eq1497 eq1472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472 eq1497
  have eq1501 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq1174 y
       grind)
    | (have r₁ := eq1499
       have r₂ := eq1174 y
       grind)
    | exact resolve eq1499 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174 eq1499
  have eq1503 : (k y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1137
       have i₂ := eq1501
       grind)
    | exact superpose eq1501 eq1137
    | exact resolve eq1137 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501
  have eq1587 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq682
       grind)
    | exact superpose eq682 eq40
    | exact resolve eq40 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq682
  have eq1588 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1587
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1587
    | exact resolve eq1587 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1587
  have eq1590 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq1588
    | exact resolve eq1588 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1588
  have eq1592 : x = (M.op (M.op x y) y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1590
       have i₂ := eq1137
       grind)
    | exact superpose eq1137 eq1590
    | exact resolve eq1590 eq1137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137 eq1590
  have eq1594 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1503 eq1592
    | exact resolve eq1592 eq1503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1592
  have eq4086 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq196 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq176 X1 X1 X0 X2
       grind)
    | exact superpose eq176 eq196
    | exact resolve eq196 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq196
  have eq13590 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) X0) = (M.op (M.op X1 (M.op X2 (k (M.op X0 X0) X0))) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4086 X0 (M.op X0 X0) (M.op X0 X0) x
       have i₂ := eq178 X0
       grind)
    | exact superpose eq178 eq4086
    | exact resolve eq4086 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq13787 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4086 (M.op X0 X1) X0 X1 (M.op x (M.op (M.op X0 X1) x))
       have i₂ := eq16 (M.op X0 X1) x x
       grind)
    | exact superpose eq16 eq4086
    | exact resolve eq4086 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4086
  have eq13953 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X2 X0)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13590 X0 X1 X2
       have i₂ := eq584 X0
       grind)
    | exact superpose eq584 eq13590
    | exact resolve eq13590 eq584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq584 eq13590
  have eq14741 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 X0) (M.op (k X0 X0) (k X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13953 (k X0 X0) X1 (M.op x (M.op X0 x))
       have i₂ := eq716 X0 x x
       grind)
    | exact superpose eq716 eq13953
    | (have j1 := eq716 X0 X1 x
       grind)
    | exact resolve eq13953 eq716
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq14837 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op X0 (σ y)) (M.op (k (σ y) (σ y)) (k (σ y) (σ y)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq701 eq13953
    | exact resolve eq13953 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq15005 : ∀ X0 : G, (k (σ y) (σ y)) = (M.op (M.op X0 (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq1025 eq14837
    | (have j1 := eq1025 (σ y)
       grind)
    | exact resolve eq14837 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14837
  have eq15061 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | exact superpose eq1025 eq14741
    | (have j0 := eq14741 X0 X1
       have j1 := eq1025 X0
       grind)
    | exact resolve eq14741 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025 eq14741
  have eq15072 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq15005 x
       have i₂ := eq1108 sF3 x
       grind)
    | exact superpose eq1108 eq15005
    | exact resolve eq15005 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15005
  have eq15101 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15061 X0 x
       have i₂ := eq1108 X0 x
       grind)
    | exact superpose eq1108 eq15061
    | (have j0 := eq15061 X0 x
       grind)
    | exact resolve eq15061 eq1108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1108 eq15061
  have eq15104 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq15072
       have r₂ := eq13 (k (σ y) (σ y)) (σ y)
       grind)
    | (have r₁ := eq15072
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq15072 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15072
  have eq15107 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq15101 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq15101 x
       have r₂ := eq13 (k x x) x
       grind)
    | (have r₁ := eq15101 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq15101 (M.op x x)
       have r₂ := eq13 (M.op (M.op x x) (M.op x x)) x
       grind)
    | exact resolve eq15101 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15101
  have eq15197 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq177 X0
       have i₂ := eq15107 X0
       grind)
    | exact superpose eq15107 eq177
    | exact resolve eq177 eq15107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq15221 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq13787 X0 X0
       have i₂ := eq15107 X0
       grind)
    | exact superpose eq15107 eq13787
    | exact resolve eq13787 eq15107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13787
  have eq15298 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq180 X0 X0
       have i₂ := eq15107 (M.op X0 X0)
       grind)
    | exact superpose eq15107 eq180
    | exact resolve eq180 eq15107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq15408 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq15298 X0
       have i₂ := eq15107 X0
       grind)
    | exact superpose eq15107 eq15298
    | exact resolve eq15298 eq15107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15298
  have eq15730 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 X0) (M.op (k X0 X0) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq13953 (k X0 X0) X1 X0
       have i₂ := eq15197 X0
       grind)
    | exact superpose eq15197 eq13953
    | exact resolve eq13953 eq15197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13953 eq15197
  have eq15740 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 X0) (k (k X0 X0) (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq15730 X0 X1
       have i₂ := eq15107 (k X0 X0)
       grind)
    | exact superpose eq15107 eq15730
    | exact resolve eq15730 eq15107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15107 eq15730
  have eq15745 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15740 X0 X1
       have i₂ := eq15408 X0
       grind)
    | exact superpose eq15408 eq15740
    | exact resolve eq15740 eq15408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15740
  have eq16597 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15221 (σ x)
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq15221
    | exact resolve eq15221 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63965 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1594 eq689
    | exact resolve eq689 eq1594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq689
  have eq63976 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq63965
       have r₂ := eq27
       grind)
    | exact resolve eq63965 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63965
  have eq63984 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq15104 eq63976
    | exact resolve eq63976 eq15104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63976
  have eq64377 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq63984 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq63984
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq63984
       grind)
    | exact resolve eq12 eq63984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63984
  have eq64410 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by grind
  clear eq64377
  have eq64427 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq15104 eq64410
    | exact resolve eq64410 eq15104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15104 eq64410
  have eq64428 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by grind
  clear eq64427
  have eq64439 : (σ x) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1594 eq64428
    | exact resolve eq64428 eq1594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594 eq64428
  have eq64448 : (τ (σ x)) = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq64439 eq115
    | exact resolve eq115 eq64439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq64439
  have eq64539 : x = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq64448
    | exact resolve eq64448 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64448
  have eq64540 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y y) := by grind
  clear eq64539
  have eq64600 : (k x x) = (M.op y x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq15745 x y
       have i₂ := eq64540
       grind)
    | exact superpose eq64540 eq15745
    | exact resolve eq15745 eq64540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15745
  have eq64617 : y = (k x x) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y y) := by
    first
    | exact superpose eq64540 eq64600
    | exact resolve eq64600 eq64540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64540 eq64600
  have eq65883 : x = (k y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = (k y y) := by
    first
    | (have i₁ := eq15408 x
       have i₂ := eq64617
       grind)
    | exact superpose eq64617 eq15408
    | exact resolve eq15408 eq64617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15408 eq64617
  have eq65902 : x = (k y y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq65883
  have eq65979 : x = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq15221 y
       have i₂ := eq65902
       grind)
    | exact superpose eq65902 eq15221
    | exact resolve eq15221 eq65902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15221 eq65902
  have eq66009 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq65979
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq65979
    | exact resolve eq65979 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65979
  have eq66069 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq66009 eq28
    | exact resolve eq28 eq66009
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq66009
  have eq66171 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq66069
    | exact resolve eq66069 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq66069
  have eq66172 : x = (M.op x y) := by grind
  clear eq66171
  have eq66189 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq66172
       grind)
    | exact superpose eq66172 eq18
    | exact resolve eq18 eq66172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq66190 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq66172
       grind)
    | exact superpose eq66172 eq22
    | exact resolve eq22 eq66172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq66172
  have eq66347 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq66190 eq20
    | exact resolve eq20 eq66190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66190
  have eq66805 : (M.op x y) = (k y y) := by
    first
    | exact superpose eq66189 eq1503
    | exact resolve eq1503 eq66189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503 eq66189
  have eq67758 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq16597 y
       have i₂ := eq66805
       grind)
    | exact superpose eq66805 eq16597
    | exact resolve eq16597 eq66805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16597 eq66805
  have eq67771 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq67758
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq67758
    | exact resolve eq67758 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq67758
  have eq67801 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq20 eq67771
    | exact resolve eq67771 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq67771
  have eq67816 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq66347 eq67801
    | exact resolve eq67801 eq66347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67801
  have eq68006 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq67816 eq26
    | exact resolve eq26 eq67816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq67816
  have eq68128 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq68006 eq27
    | exact resolve eq27 eq68006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq68006
  have eq68369 : False := by grind
  exact eq68369

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_y_pxx_y_pyx_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) (k (M.op X0 X0) X0)) = (k (k (M.op X0 X0) X0) (M.op X0 X0)) := by
    intro X0
    grind
  have eq37 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (k (M.op X0 X0) X0)) := by
    intro X0 X1 X2
    grind
  have eq38 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq72 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq14 (τ X1) (τ X0)
       grind)
    | exact superpose eq14 eq38
    | (have j1 := eq14 (τ X1) (τ X0)
       grind)
    | exact resolve eq38 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) (k (M.op X0 X0) X0)) := by
    intro X0
    grind
  have eq80 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq9
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq170 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq25 X0
       grind)
    | exact superpose eq25 eq24
    | exact resolve eq24 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (k (M.op X1 X1) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq37 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq24 X1 X1 X0 X2
       grind)
    | exact superpose eq24 eq37
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq37
  have eq217 : ∀ X0 : G, (k (M.op X0 X0) X0) = (M.op (k (M.op X0 X0) X0) (k (k (M.op X0 X0) X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25 (k (M.op X0 X0) X0)
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq25
    | exact resolve eq25 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq251 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (M.op (σ X0) X2)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq60 X0 X0
       grind)
    | exact superpose eq60 eq9
    | (have j1 := eq60 X0 X0
       grind)
    | exact resolve eq9 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  clear eq60
  have eq271 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq252 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252
  have eq272 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (M.op X1 (M.op (σ X0) X2)) (σ (k X0 X0))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq251 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq278 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq271 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq271
    | (have j0 := eq271 X0
       grind)
    | exact resolve eq271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq334 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    grind
  have eq693 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq78 X0
       have i₂ := eq334 X0
       grind)
    | exact superpose eq334 eq78
    | exact resolve eq78 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq935 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq170 X0 X0 X1
       have i₂ := eq80 X0 X0
       grind)
    | exact superpose eq80 eq170
    | exact resolve eq170 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq170
  have eq1078 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq180 X0 X1 X2 X3
       have i₂ := eq334 X1
       grind)
    | exact superpose eq334 eq180
    | exact resolve eq180 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq1766 : ∀ X0 : G, (M.op X0 (k X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq217 X0
       have i₂ := eq334 X0
       grind)
    | exact superpose eq334 eq217
    | exact resolve eq217 eq334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq334
  have eq1796 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X1 (M.op X0 X2)) (σ (k (τ X0) (τ X0)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq272 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq272
    | exact resolve eq272 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272
  have eq1842 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 (σ (τ X0)))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1796 X0 X1 X2
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1796
    | (have j0 := eq1796 X0 X1 X2
       grind)
    | exact resolve eq1796 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796
  have eq1845 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1842 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1842
    | (have j0 := eq1842 X0 X1 X2
       grind)
    | exact resolve eq1842 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1842
  have eq1888 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1845 X0 x (M.op (k X0 X0) x)
       have i₂ := eq1078 X0 (k X0 X0) x x
       grind)
    | exact superpose eq1078 eq1845
    | (have j0 := eq1845 X0 x x
       grind)
    | exact resolve eq1845 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078 eq1845
  have eq2245 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 X0) X1 (k X0 X0)
       have i₂ := eq1888 X0
       grind)
    | exact superpose eq1888 eq9
    | (have j1 := eq1888 X0
       grind)
    | exact resolve eq9 eq1888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888
  have eq2409 : ∀ X0 : G, (k (k (σ X0) (σ X0)) (σ X0)) = (M.op (k (σ X0) (σ X0)) (k (σ X0) (σ X0))) ∨ (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq34 (σ X0)
       have i₂ := eq278 X0
       grind)
    | exact superpose eq278 eq34
    | (have j1 := eq278 X0
       grind)
    | exact resolve eq34 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq278
  have eq2442 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (k (σ (k X0 X0)) (σ X0)) ∨ (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq2409 x
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq2409
    | (have j0 := eq2409 X0
       grind)
    | exact resolve eq2409 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2409
  have eq2447 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) ∨ (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq2442 X0
       have i₂ := eq15 (k X0 X0) X0
       grind)
    | exact superpose eq15 eq2442
    | (have j0 := eq2442 X0
       grind)
    | exact resolve eq2442 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2442
  have eq2448 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (σ (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have j0 := eq2447 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2447
  have eq2977 : ∀ X0 X1 : G, (M.op X0 (k X0 X0)) = X0 ∨ (k X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1766 X0
       have i₂ := eq2245 X0 X1
       grind)
    | exact superpose eq2245 eq1766
    | (have j1 := eq2245 X0 X1
       grind)
    | exact resolve eq1766 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1766 eq2245
  have eq10961 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2977 X0 x
       have i₂ := eq935 X0 x
       grind)
    | exact superpose eq935 eq2977
    | (have j0 := eq2977 X0 x
       grind)
    | exact resolve eq2977 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2977
  have eq10972 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq13 (k X0 X0) X0
       have i₂ := eq10961 X0
       grind)
    | exact superpose eq10961 eq13
    | (have j0 := eq13 (k X0 X0) X0
       have j1 := eq10961 X0
       grind)
    | (have r₁ := eq13 (k X0 X0) X0
       have r₂ := eq10961 X0
       grind)
    | exact resolve eq13 eq10961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10961
  have eq11009 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (k (k X0 X0) X0) = X0 := by
    intro X0
    first
    | (have j0 := eq10972 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10972
  have eq11010 : ∀ X0 : G, (k (k X0 X0) X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11009 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11009
  have eq29963 : ∀ X0 : G, (σ (k (τ (k X0 X0)) (τ X0))) = (M.op (σ (τ (k X0 X0))) (σ (τ (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq2448 (τ X0)
       have i₂ := eq38 X0 X0
       grind)
    | exact superpose eq38 eq2448
    | exact resolve eq2448 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2448
  have eq30218 : ∀ X0 : G, (σ (k (τ (k X0 X0)) (τ X0))) = (M.op (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq29963 X0
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq29963
    | exact resolve eq29963 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29963
  have eq30272 : ∀ X0 : G, (k (k X0 X0) (σ (τ X0))) = (M.op (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq30218 X0
       have i₂ := eq18 (k X0 X0) (τ X0)
       grind)
    | exact superpose eq18 eq30218
    | exact resolve eq30218 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30218
  have eq30291 : ∀ X0 : G, (k (k X0 X0) X0) = (M.op (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq30272 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30272
    | exact resolve eq30272 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30272
  have eq30398 : ∀ X0 : G, (k X0 X0) = (M.op (k (k X0 X0) X0) (k (k X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq80 (k X0 X0) (k X0 X0)
       have i₂ := eq30291 X0
       grind)
    | exact superpose eq30291 eq80
    | exact resolve eq80 eq30291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq30291
  have eq34241 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq30398 X0
       have i₂ := eq11010 X0
       grind)
    | exact superpose eq11010 eq30398
    | (have j1 := eq11010 X0
       grind)
    | exact resolve eq30398 eq11010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11010 eq30398
  have eq34365 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq34241 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34241
  have eq34602 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq34365 (σ X0)
       grind)
    | exact superpose eq34365 eq15
    | exact resolve eq15 eq34365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34608 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq38 X0 X0
       have i₂ := eq34365 (τ X0)
       grind)
    | exact superpose eq34365 eq38
    | exact resolve eq38 eq34365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq34644 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34608 X0
       have i₂ := eq34365 X0
       grind)
    | exact superpose eq34365 eq34608
    | exact resolve eq34608 eq34365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34608
  have eq34650 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34602 X0
       have i₂ := eq34365 X0
       grind)
    | exact superpose eq34365 eq34602
    | exact resolve eq34602 eq34365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34365 eq34602
  have eq34781 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq25 (τ X0)
       have i₂ := eq34644 X0
       grind)
    | exact superpose eq34644 eq25
    | exact resolve eq25 eq34644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq35312 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq693 (σ X0)
       have i₂ := eq34650 X0
       grind)
    | exact superpose eq34650 eq693
    | exact resolve eq693 eq34650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3381678 : ∀ X0 X1 : G, (τ X1) = (τ (M.op X0 X0)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq34644 X0
       grind)
    | exact superpose eq34644 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq34644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq34644
  have eq3382252 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X1) (τ X0)) ∨ (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34781 X1
       have i₂ := eq3381678 X1 X0
       grind)
    | (have i₁ := eq34781 X0
       have i₂ := eq3381678 X0 (M.op X0 X0)
       grind)
    | exact superpose eq3381678 eq34781
    | (have j1 := eq3381678 X1 X0
       grind)
    | exact resolve eq34781 eq3381678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34781 eq3381678
  have eq3382534 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq3382252 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3382252
  have eq3383717 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (τ (k X1 (σ X0))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3382534 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3382534
    | exact resolve eq3382534 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3382534
  have eq3386084 : ∀ X0 X1 : G, (M.op X0 (τ X1)) = (k (τ X1) X0) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3383717 X0 X1
       have i₂ := eq23 X1 X0
       grind)
    | exact superpose eq23 eq3383717
    | (have j0 := eq3383717 X0 X1
       grind)
    | exact resolve eq3383717 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq3383717
  have eq3388092 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3386084 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3386084
    | exact resolve eq3386084 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3388152 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq3386084 X0 X1
       grind)
    | exact superpose eq3386084 eq18
    | (have j1 := eq3386084 X0 X1
       grind)
    | exact resolve eq18 eq3386084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq3386084
  have eq3389180 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3388092 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3388092
    | (have j0 := eq3388092 (σ X0) (σ X1)
       grind)
    | exact resolve eq3388092 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3388092
  have eq3391910 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3388152 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3388152
    | exact resolve eq3388152 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3388152
  have eq3393025 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3391910 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq3391910
    | (have j0 := eq3391910 X0 X1
       grind)
    | exact resolve eq3391910 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3391910
  have eq3404338 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3389180 y x
       grind)
    | exact superpose eq3389180 eq16
    | (have j1 := eq3389180 y x
       grind)
    | exact resolve eq16 eq3389180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3389180
  have eq3407698 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3404338
       have i₂ := eq3393025 y x
       grind)
    | exact superpose eq3393025 eq3404338
    | (have j1 := eq3393025 (σ y) (σ x)
       grind)
    | (have r₁ := eq3404338
       have r₂ := eq3393025 y x
       grind)
    | exact resolve eq3404338 eq3393025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3393025 eq3404338
  have eq3407711 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3407698
  have eq3407742 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq935 y x
       have i₂ := eq3407711
       grind)
    | exact superpose eq3407711 eq935
    | exact resolve eq935 eq3407711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3414966 : (σ (M.op x y)) ≠ (σ x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3407742
       grind)
    | exact superpose eq3407742 eq16
    | exact resolve eq16 eq3407742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3407742
  have eq3416401 : (σ x) ≠ (σ x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3414966
       have i₂ := eq3407711
       grind)
    | exact superpose eq3407711 eq3414966
    | exact resolve eq3414966 eq3407711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3407711 eq3414966
  have eq3416416 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq3416401
  have eq3419596 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq935 (σ y) (σ x)
       have i₂ := eq3416416
       grind)
    | exact superpose eq3416416 eq935
    | exact resolve eq935 eq3416416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935
  have eq3420725 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3419596
       have i₂ := eq34650 y
       grind)
    | exact superpose eq34650 eq3419596
    | exact resolve eq3419596 eq34650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34650 eq3419596
  have eq3438770 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3416416
       have i₂ := eq3420725
       grind)
    | exact superpose eq3420725 eq3416416
    | exact resolve eq3416416 eq3420725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3416416 eq3420725
  have eq3439675 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq3438770
  have eq3442132 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq3439675
       grind)
    | exact superpose eq3439675 eq10
    | exact resolve eq10 eq3439675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3439675
  have eq3442683 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3442132
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3442132
    | exact resolve eq3442132 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3442132
  have eq3442684 : x = (M.op y y) := by grind
  clear eq3442683
  have eq3447423 : x = (M.op x y) := by
    first
    | (have i₁ := eq693 y
       have i₂ := eq3442684
       grind)
    | exact superpose eq3442684 eq693
    | exact resolve eq693 eq3442684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq693
  have eq3447490 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq35312 y
       have i₂ := eq3442684
       grind)
    | exact superpose eq3442684 eq35312
    | exact resolve eq35312 eq3442684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35312 eq3442684
  have eq3553266 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3447490
       grind)
    | exact superpose eq3447490 eq16
    | exact resolve eq16 eq3447490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3447490
  have eq3554618 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq3553266
       have i₂ := eq3447423
       grind)
    | exact superpose eq3447423 eq3553266
    | exact resolve eq3553266 eq3447423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3447423 eq3553266
  have eq3554619 : False := by grind
  exact eq3554619

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,X) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxx_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a a :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op X0 X3)) X1 (M.op X0 X0)
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 (M.op x (M.op X0 x)) X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq49 : ∀ X0 : G, (M.op (k (M.op X0 X0) X0) (M.op X0 X0)) = X0 := by
    intro X0
    grind
  have eq52 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (k (M.op X0 X0) X0)) := by
    intro X0 X1 X2
    grind
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq47 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq96 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq20 X0 (τ X0)
       have i₂ := eq53 (τ X0)
       grind)
    | exact superpose eq53 eq20
    | exact resolve eq20 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq97 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq96 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq96
    | exact resolve eq96 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq105 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq97 X0
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq97
    | exact resolve eq97 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq97
  have eq109 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq105 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq105
    | exact resolve eq105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq150 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0)
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq26
    | exact resolve eq26 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq163 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (k (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X1) X2 (M.op X0 X0)
       have i₂ := eq9 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq9 eq52
    | exact resolve eq52 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op (k (M.op X0 X0) X0) (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    grind
  have eq215 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq25
    | exact resolve eq25 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq25 (M.op X1 X0) X1 X2 (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))
       have i₂ := eq25 X0 X1 X2 X3
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (k (M.op X1 X1) X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq52 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq25 X1 X1 X0 X2
       grind)
    | exact superpose eq25 eq52
    | exact resolve eq52 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq262 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq67 X0 X1
       have i₂ := eq109 X1
       grind)
    | exact superpose eq109 eq67
    | (have j0 := eq67 X0 X1
       grind)
    | exact resolve eq67 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq275 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) X1 (σ (M.op X0 X0))
       have i₂ := eq150 X0
       grind)
    | exact superpose eq150 eq9
    | exact resolve eq9 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq276 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq275 X0 X1
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq275
    | exact resolve eq275 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275
  have eq293 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq262 x y
       grind)
    | exact superpose eq262 eq16
    | (have j1 := eq262 x y
       grind)
    | exact resolve eq16 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262
  have eq347 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op (M.op X1 (σ (τ X0))) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq276 (τ X0) X1
       have i₂ := eq105 X0
       grind)
    | exact superpose eq105 eq276
    | exact resolve eq276 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105 eq276
  have eq353 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq347 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq347
    | exact resolve eq347 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq347
  have eq387 : ∀ X0 : G, (k (M.op X0 X0) X0) = X0 := by
    intro X0
    grind
  have eq398 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq26 (M.op X0 X0)
       have i₂ := eq353 X0 X0
       grind)
    | exact superpose eq353 eq26
    | exact resolve eq26 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq150 (M.op X0 X0)
       have i₂ := eq353 X0 X0
       grind)
    | exact superpose eq353 eq150
    | exact resolve eq150 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq809 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq293
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq293
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq293
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq293
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq293 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq810 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq809
  have eq1028 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X1)) (k (M.op X1 X1) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq215 X1 X0 X1
       grind)
    | exact superpose eq215 eq52
    | exact resolve eq52 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1040 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X0 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1028 X0 X1 X2
       have i₂ := eq387 X1
       grind)
    | exact superpose eq387 eq1028
    | exact resolve eq1028 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028
  have eq1390 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq232 X0 X1 X2 X3
       have i₂ := eq387 X1
       grind)
    | exact superpose eq387 eq232
    | exact resolve eq232 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq1473 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1390 (M.op X0 X1) X0 X1 (M.op X0 X1)
       have i₂ := eq26 (M.op X0 X1)
       grind)
    | exact superpose eq26 eq1390
    | exact resolve eq1390 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1529 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1473 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq353 X0 X1
       grind)
    | exact superpose eq353 eq1473
    | exact resolve eq1473 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353 eq1473
  have eq2431 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq163 X0 X1 X2
       have i₂ := eq387 (M.op X0 X1)
       grind)
    | exact superpose eq387 eq163
    | exact resolve eq163 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq2562 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X4 (M.op X1 (M.op X2 (M.op X0 X3)))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2431 (M.op X3 (M.op X0 (M.op X1 X2))) X1 X2
       have i₂ := eq1390 X0 X1 X2 X3
       grind)
    | exact superpose eq1390 eq2431
    | exact resolve eq2431 eq1390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1390 eq2431
  have eq2693 : ∀ X0 X1 X2 X3 X4 : G, (k (M.op X0 X0) X0) = (M.op (M.op X4 (M.op X1 (M.op X2 (M.op X0 X3)))) (M.op X0 X0)) := by
    intro X0 X1 X2 X3 X4
    grind
  clear eq2562
  have eq2707 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X4 (M.op X1 (M.op X2 (M.op X0 X3)))) (M.op X0 X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2693 X0 X1 X2 X3 X4
       have i₂ := eq387 X0
       grind)
    | exact superpose eq387 eq2693
    | exact resolve eq2693 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2693
  have eq5029 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op (k (M.op X0 X0) X0) (M.op (M.op (M.op X0 X0) X2) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq207 X0 X1 X2
       have i₂ := eq1529 (M.op (M.op X0 X0) X2) X1
       grind)
    | exact superpose eq1529 eq207
    | exact resolve eq207 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq5030 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op (M.op X0 X0) X2) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5029 X0 X1 X2
       have i₂ := eq387 X0
       grind)
    | exact superpose eq387 eq5029
    | exact resolve eq5029 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387 eq5029
  have eq5050 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X1)) = (M.op X1 (M.op (M.op X0 X1) (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5030 X0 X1 (M.op (M.op X1 X0) (M.op X1 X0))
       have i₂ := eq215 X0 X1 X0
       grind)
    | exact superpose eq215 eq5030
    | exact resolve eq5030 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq5030
  have eq5232 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op (M.op X5 (M.op X4 X1)) (M.op (M.op X0 (M.op X1 X2)) (M.op X3 (M.op X0 (M.op X1 X2))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq218 X0 X1 X2 X3 X4 X5
       have i₂ := eq1529 (M.op X0 (M.op X1 X2)) X3
       grind)
    | exact superpose eq1529 eq218
    | exact resolve eq218 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq5437 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5232 (M.op X1 X2) X1 X2 (k (M.op (M.op X1 X2) (M.op X1 X2)) (M.op X1 X2)) x x
       have i₂ := eq49 (M.op X1 X2)
       grind)
    | exact superpose eq49 eq5232
    | exact resolve eq5232 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq5232
  have eq5526 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op (M.op X0 X1) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5437 X0 X1 X2 X3
       have i₂ := eq398 (M.op X0 X1)
       grind)
    | exact superpose eq398 eq5437
    | exact resolve eq5437 eq398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5437
  have eq5575 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op X3 X0)) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq5526 X0 X1 X2 X3
       have i₂ := eq1529 X1 X0
       grind)
    | exact superpose eq1529 eq5526
    | exact resolve eq5526 eq1529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529 eq5526
  have eq10895 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X4 (M.op X1 (M.op X2 X0)))) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5575 (M.op X2 (M.op X0 X1)) X1 X2 X3
       have i₂ := eq1040 X0 X1 X2
       grind)
    | exact superpose eq1040 eq5575
    | exact resolve eq5575 eq1040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040 eq5575
  have eq11235 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X4 (M.op X1 (M.op X2 X0)))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq10895 X0 X1 X2 X3 X4
       have i₂ := eq26 X0
       grind)
    | exact superpose eq26 eq10895
    | exact resolve eq10895 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10895
  have eq14733 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 (M.op X4 (M.op X5 (M.op X0 (M.op X1 X2))))) (M.op X2 X2)) = X2 := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq2707 X2 X4 X5 (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) X3
       have i₂ := eq5050 X1 X2 X0
       grind)
    | exact superpose eq5050 eq2707
    | exact resolve eq2707 eq5050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2707 eq5050
  have eq20510 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq810
       grind)
    | exact superpose eq810 eq16
    | exact resolve eq16 eq810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq810
  have eq20511 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq20510
       have r₂ := eq109 x
       grind)
    | exact resolve eq20510 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20510
  have eq270366 : ∀ X0 X1 X2 X3 : G, y = (M.op (M.op X0 (M.op X1 (M.op X2 (M.op X3 x)))) x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14733 X0 y y X3 x x
       have i₂ := eq20511
       grind)
    | exact superpose eq20511 eq14733
    | exact resolve eq14733 eq20511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14733 eq20511
  have eq270411 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq270366 x x x x
       have i₂ := eq11235 x x x x x
       grind)
    | exact superpose eq11235 eq270366
    | exact resolve eq270366 eq11235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11235 eq270366
  have eq414820 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq270411
       grind)
    | exact superpose eq270411 eq10
    | exact resolve eq10 eq270411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270411
  have eq415154 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq414820
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq414820
    | exact resolve eq414820 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414820
  have eq415157 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq415154
       grind)
    | exact superpose eq415154 eq16
    | exact resolve eq16 eq415154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415154
  have eq415158 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq415157
       have r₂ := eq109 x
       grind)
    | exact resolve eq415157 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq415157
  have eq415164 : x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq26 x
       have i₂ := eq415158
       grind)
    | exact superpose eq415158 eq26
    | exact resolve eq26 eq415158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq415169 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq150 x
       have i₂ := eq415158
       grind)
    | exact superpose eq415158 eq150
    | exact resolve eq150 eq415158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq415158
  have eq463431 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq415169
       grind)
    | exact superpose eq415169 eq16
    | exact resolve eq16 eq415169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415169
  have eq463950 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq463431
       have i₂ := eq415164
       grind)
    | exact superpose eq415164 eq463431
    | exact resolve eq463431 eq415164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415164 eq463431
  have eq463981 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq463950
  have eq463982 : (σ x) = (σ (M.op y y)) := by grind
  clear eq463981
  have eq464061 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq403 y
       have i₂ := eq463982
       grind)
    | exact superpose eq463982 eq403
    | exact resolve eq403 eq463982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq464131 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq463982
       grind)
    | exact superpose eq463982 eq10
    | exact resolve eq10 eq463982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq463982
  have eq464626 : x = (M.op y y) := by
    first
    | (have i₁ := eq464131
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq464131
    | exact resolve eq464131 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464131
  have eq464882 : x = (M.op x y) := by
    first
    | (have i₁ := eq398 y
       have i₂ := eq464626
       grind)
    | exact superpose eq464626 eq398
    | exact resolve eq398 eq464626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq398 eq464626
  have eq502679 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq464061
       grind)
    | exact superpose eq464061 eq16
    | exact resolve eq16 eq464061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464061
  have eq503181 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq502679
       have i₂ := eq464882
       grind)
    | exact superpose eq464882 eq502679
    | exact resolve eq502679 eq464882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464882 eq502679
  have eq503182 : False := by grind
  exact eq503182

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pxy_pxy_pxx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq32 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = (k X2 X0) := by
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
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq46 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq48 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X2 X2) = (M.op X2 X0) ∨ (M.op X2 X0) = (k X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq32 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq46 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq118 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq619 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq48 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq620 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq619 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq625 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq620 X0 X1
       have j1 := eq118 X0 X1
       grind)
    | (have r₁ := eq620 X0 X1
       have r₂ := eq118 X0 X1
       grind)
    | (have r₁ := eq620 X1 X1
       have r₂ := eq118 X1 X1
       grind)
    | exact resolve eq620 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq620
  have eq1156 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq625 (σ X0) (σ X1)
       grind)
    | exact superpose eq625 eq15
    | exact resolve eq15 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1159 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1156 X0 X1
       have i₂ := eq625 X0 X1
       grind)
    | exact superpose eq625 eq1156
    | exact resolve eq1156 eq625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625 eq1156
  have eq1163 : False := by grind
  exact eq1163
