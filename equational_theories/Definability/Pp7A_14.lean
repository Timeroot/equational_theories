import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1845`: `x = (x ◇ (x ◇ y)) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_x_pyy_pxy_Equation1845 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1845 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1845.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
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
  have eq57 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
       have i₂ := eq14 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
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
  have eq79 : (k (σ x) (σ (M.op x y))) = (σ (M.op x (M.op x y))) ∨ (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x sF0
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x (M.op x y)
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq78
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq78
    | exact resolve eq78 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq83
    | exact resolve eq83 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq86 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq85
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq85
    | exact resolve eq85 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq105 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq142 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq120 eq16
    | exact resolve eq16 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq193 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq196 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq60 eq14
    | exact resolve eq14 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq329 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 (M.op X0 X1)) (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq62 (M.op X0 (M.op X0 X1)) (M.op x x) X3
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq62
    | exact resolve eq62 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq330 : ∀ X1 : G, (M.op (M.op x (M.op x y)) x) = (M.op (M.op x (M.op x y)) (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq59 eq62
    | exact resolve eq62 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq334 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq62 X0 x X3
       have i₂ := eq62 X0 x X1
       grind)
    | (have i₁ := eq62 x x x
       have i₂ := eq62 x X1 x
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq340 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 X1 x
       have i₂ := eq62 X0 X2 x
       grind)
    | (have i₁ := eq62 X1 X1 X1
       have i₂ := eq62 X1 X1 X2
       grind)
    | exact superpose eq62 eq62
    | exact resolve eq62 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X3 X3)) = X0 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X0 x X3
       have i₂ := eq62 X0 x X1
       grind)
    | (have i₁ := eq14 x x x
       have i₂ := eq62 x X1 x
       grind)
    | exact superpose eq62 eq14
    | exact resolve eq14 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq59 eq330
    | exact resolve eq330 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq330
  have eq357 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq329 X0 X1 x
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq329
    | exact resolve eq329 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq375 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq105 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq105
    | (have j0 := eq105 (σ X0)
       grind)
    | exact resolve eq105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq446 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq357 X0 x
       have i₂ := eq62 X0 x X1
       grind)
    | (have i₁ := eq357 x x
       have i₂ := eq62 x X1 x
       grind)
    | exact superpose eq62 eq357
    | exact resolve eq357 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq72 X1 X0
       grind)
    | (have i₁ := eq12 (σ X1) (σ X1)
       have i₂ := eq72 X0 X1
       grind)
    | exact superpose eq72 eq12
    | (have j0 := eq12 (σ X0) (σ X0)
       have j1 := eq72 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq72 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq72 X0 X0
       grind)
    | exact resolve eq12 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq544 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq72 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq547 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq528 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528
  have eq548 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq547 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq552 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq548 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq548
    | (have j0 := eq548 X0 X1
       grind)
    | exact resolve eq548 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548
  have eq655 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq215 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq215
    | exact resolve eq215 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq3374 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq375 X0
       grind)
    | exact superpose eq375 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq375 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq375 X0
       grind)
    | exact resolve eq13 eq375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3396 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq375 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq3399 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3374 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq3374 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq3374 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3374
  have eq7007 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq552 X0 X1
       have j1 := eq544 X1 X0
       grind)
    | (have r₁ := eq552 X1 X0
       have r₂ := eq544 X0 X1
       grind)
    | (have r₁ := eq552 X1 X1
       have r₂ := eq544 X1 X1
       grind)
    | exact resolve eq552 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544 eq552
  have eq7180 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq7007 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7007
    | (have j0 := eq7007 y X0
       grind)
    | exact resolve eq7007 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7181 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (M.op (σ X0) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq7007
    | (have j0 := eq7007 (M.op x y) X0
       grind)
    | exact resolve eq7007 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7210 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ (k X0 X1))) = (M.op (σ X0) (M.op X2 X2)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 (σ X0) (σ X1) X2
       have i₂ := eq7007 X1 X0
       grind)
    | exact superpose eq7007 eq62
    | (have j1 := eq7007 X1 X1
       grind)
    | exact resolve eq62 eq7007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq7007
  have eq12412 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3399 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq3399
    | (have j0 := eq3399 (τ X0) X1
       grind)
    | exact resolve eq3399 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq3399
  have eq12419 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12412 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq12412
    | (have j0 := eq12412 X0 X1
       grind)
    | exact resolve eq12412 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12412
  have eq12425 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12419 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq12419
    | (have j0 := eq12419 X0 X1
       grind)
    | exact resolve eq12419 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12419
  have eq12434 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12425 (τ X0) X1
       have i₂ := eq655 X0 X0
       grind)
    | exact superpose eq655 eq12425
    | (have j0 := eq12425 (τ X0) X1
       grind)
    | exact resolve eq12425 eq655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq15542 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq7180 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7180
    | (have j0 := eq7180 x
       grind)
    | exact resolve eq7180 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7180
  have eq15558 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq15542
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq15542
    | exact resolve eq15542 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15542
  have eq15574 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq15558
    | exact resolve eq15558 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15558
  have eq15716 : (σ (k x (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq7181 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7181
    | (have j0 := eq7181 x
       grind)
    | exact resolve eq7181 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7181
  have eq15732 : (k (σ x) (σ (M.op x y))) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq45 eq15716
    | exact resolve eq15716 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq15716
  have eq16199 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq86 eq15574
    | exact resolve eq15574 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq16204 : (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq16199
       have r₂ := eq27
       grind)
    | exact resolve eq16199 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16199
  have eq16223 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq16204 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq16204
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq16204
       grind)
    | exact resolve eq13 eq16204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16236 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (M.op X1 X1)) = X0 ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | exact superpose eq16204 eq344
    | exact resolve eq344 eq16204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq16258 : ∀ X0 : G, (M.op x y) = (M.op y y) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq16223 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16223
  have eq16503 : ∀ X0 X1 : G, y ≠ (M.op x y) ∨ (k X0 y) = X0 ∨ (k X1 (σ y)) = X1 ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq16258 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq16258 (M.op X1 X1)
       grind)
    | exact superpose eq16258 eq13
    | (have j0 := eq13 X0 y
       have j1 := eq16258 X1
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq16258 X0
       grind)
    | exact resolve eq13 eq16258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16258
  have eq16541 : ∀ X0 X1 : G, y ≠ (M.op x y) ∨ (k X0 y) = X0 ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq16503 X0 X1
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq16503 X0 X1
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq16503 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16503
  have eq19660 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) (σ y)) ∨ (k X0 (M.op (σ y) (σ y))) = X0 ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq16236 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq16236 X0 x
       grind)
    | exact resolve eq13 eq16236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16236
  have eq19735 : ∀ X0 : G, (k X0 (M.op (σ y) (σ y))) = X0 ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq19660 X0
       grind)
    | (have r₁ := eq19660 X0
       have r₂ := eq16204
       grind)
    | exact resolve eq19660 eq16204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19660
  have eq19818 : ∀ X0 : G, (τ (M.op (σ y) (σ y))) ≠ (τ (M.op (σ y) (σ y))) ∨ (k X0 (τ (M.op (σ y) (σ y)))) = X0 ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq19735 eq12434
    | (have j0 := eq12434 (M.op (σ y) (σ y)) X0
       grind)
    | exact resolve eq12434 eq19735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19735
  have eq19848 : ∀ X0 : G, (k X0 (τ (M.op (σ y) (σ y)))) = X0 ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq19818 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19818
  have eq21844 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq16204 eq19848
    | exact resolve eq19848 eq16204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16204 eq19848
  have eq21924 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq21844 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21844
  have eq21950 : ∀ X0 : G, (k X0 y) = X0 ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq29 eq21924
    | exact resolve eq21924 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21924
  have eq21967 : ∀ X0 : G, (M.op x y) = (M.op y y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq21950 X0
       have j1 := eq13 X0 y
       grind)
    | (have r₁ := eq21950 X0
       have r₂ := eq13 X0 y
       grind)
    | exact resolve eq21950 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21950
  have eq21974 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = (M.op x y) ∨ (M.op x y) = (k X0 y) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq21967 X0
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq21967 (M.op X1 X1)
       grind)
    | exact superpose eq21967 eq12
    | (have j1 := eq21967 X1
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq21967 X0
       grind)
    | exact resolve eq12 eq21967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21967
  have eq42573 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq21974 x X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq21974
    | (have j0 := eq21974 x X0
       grind)
    | (have r₁ := eq21974 x x
       have r₂ := eq18
       grind)
    | exact resolve eq21974 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21974
  have eq42580 : ∀ X0 : G, (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq42573 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42573
  have eq42585 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq44
       have i₂ := eq42580 X0
       grind)
    | (have i₁ := eq44
       have i₂ := eq42580 x
       grind)
    | exact superpose eq42580 eq44
    | (have j1 := eq42580 X0
       grind)
    | exact resolve eq44 eq42580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq42580
  have eq42605 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq42585
    | (have j0 := eq42585 X0
       grind)
    | exact resolve eq42585 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42585
  have eq42873 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq15574
       have i₂ := eq42605 (k sF2 sF3)
       grind)
    | exact superpose eq42605 eq15574
    | (have j1 := eq42605 X0
       grind)
    | exact resolve eq15574 eq42605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15574 eq42605
  have eq42880 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq42873 X0
       grind)
    | (have r₁ := eq42873 X0
       have r₂ := eq27
       grind)
    | exact resolve eq42873 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42873
  have eq42915 : ∀ X0 X1 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq42880 (M.op X1 X1)
       grind)
    | exact superpose eq42880 eq13
    | (have j0 := eq13 X0 (σ y)
       have j1 := eq42880 X1
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq42880 X0
       grind)
    | exact resolve eq13 eq42880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42880
  have eq42987 : ∀ X0 X1 : G, (k X0 (σ y)) = X0 ∨ y = (M.op x y) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq42915 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42915
  have eq43007 : ∀ X0 X1 : G, (k X1 y) = X1 ∨ (k X0 (σ y)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq42987 X0 X1
       have j1 := eq16541 X1 X0
       grind)
    | (have r₁ := eq42987 X0 X1
       have r₂ := eq16541 X0 X1
       grind)
    | exact resolve eq42987 eq16541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16541 eq42987
  have eq43350 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq3396 y
       have i₂ := eq43007 X0 y
       grind)
    | exact superpose eq43007 eq3396
    | (have j0 := eq3396 y
       have j1 := eq43007 X0 x
       grind)
    | exact resolve eq3396 eq43007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43007
  have eq43419 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq43350 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43350
  have eq43480 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq43419 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq43419
    | (have j0 := eq43419 X0
       grind)
    | exact resolve eq43419 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq43419
  have eq43593 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq43480 X0
       have j1 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq43480 X0
       have r₂ := eq13 X0 (σ y)
       grind)
    | exact resolve eq43480 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43480
  have eq43707 : ∀ X0 : G, (τ (σ y)) ≠ (τ (σ y)) ∨ (k X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq43593 eq12434
    | (have j0 := eq12434 (σ y) X0
       grind)
    | exact resolve eq12434 eq43593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12434
  have eq43710 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq43593 eq105
    | (have j0 := eq105 (σ y)
       grind)
    | exact resolve eq105 eq43593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43593
  have eq43770 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq43710
  have eq43773 : ∀ X0 : G, (k X0 (τ (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq43707 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43707
  have eq43833 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq29 eq43773
    | exact resolve eq43773 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq43773
  have eq43978 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) (σ y)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq43770 eq14
    | exact resolve eq14 eq43770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43979 : x = (M.op (M.op x (M.op x y)) (σ y)) := by
    first
    | exact superpose eq43770 eq59
    | exact resolve eq59 eq43770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq43986 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq43770 eq196
    | exact resolve eq196 eq43770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43988 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq43770 eq334
    | exact resolve eq334 eq43770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334 eq43770
  have eq44060 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq43986
    | exact resolve eq43986 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq43986
  have eq44153 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq105 y
       have i₂ := eq43833 y
       grind)
    | exact superpose eq43833 eq105
    | (have j0 := eq105 y
       grind)
    | exact resolve eq105 eq43833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43833
  have eq44213 : y = (M.op y y) := by grind
  clear eq44153
  have eq44487 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq193 y
       have i₂ := eq44213
       grind)
    | exact superpose eq44213 eq193
    | exact resolve eq193 eq44213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq44489 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) y) := by
    first
    | (have i₁ := eq196 y
       have i₂ := eq44213
       grind)
    | exact superpose eq44213 eq196
    | exact resolve eq196 eq44213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44496 : ∀ X0 : G, (M.op (M.op X0 y) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq446 X0 y
       have i₂ := eq44213
       grind)
    | exact superpose eq44213 eq446
    | exact resolve eq446 eq44213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446 eq44213
  have eq44560 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq44060 eq44489
    | exact resolve eq44489 eq44060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44489
  have eq44561 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq44487
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq44487
    | exact resolve eq44487 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq44487
  have eq44613 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq44561 eq356
    | exact resolve eq356 eq44561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq47028 : x = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq44561 eq43979
    | exact resolve eq43979 eq44561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43979
  have eq47042 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq47028 eq340
    | exact resolve eq340 eq47028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47028
  have eq47053 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq44613 eq47042
    | exact resolve eq47042 eq44613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44613 eq47042
  have eq57407 : ∀ X0 : G, (M.op X0 y) = (M.op (M.op (M.op X0 y) X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq43978 (M.op X0 y) X0
       have i₂ := eq44496 X0
       grind)
    | exact superpose eq44496 eq43978
    | exact resolve eq43978 eq44496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43978
  have eq57699 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq57407 X0
       have i₂ := eq44496 X0
       grind)
    | exact superpose eq44496 eq57407
    | exact resolve eq57407 eq44496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44496 eq57407
  have eq59414 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) := by
    intro X0 X1
    first
    | exact superpose eq57699 eq43988
    | exact resolve eq43988 eq57699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43988 eq57699
  have eq98059 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq44561 eq79
    | exact resolve eq79 eq44561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq98060 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x (M.op x y)) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq98059
    | exact resolve eq98059 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98059
  have eq98061 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq44561 eq98060
    | exact resolve eq98060 eq44561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44561 eq98060
  have eq98062 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq98061
  have eq98063 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq15732 eq98062
    | exact resolve eq98062 eq15732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15732
  have eq98068 : (τ (σ (M.op x y))) = (k x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq98062 eq57
    | exact resolve eq57 eq98062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq98062
  have eq98084 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq30 eq98068
    | exact resolve eq98068 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98068
  have eq119931 : ∀ X0 X1 : G, (M.op (σ X0) (σ (k X0 X1))) = (M.op (σ X0) y) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7210 X0 X1 x
       have i₂ := eq59414 (σ X0) x
       grind)
    | exact superpose eq59414 eq7210
    | (have j0 := eq7210 X0 X1 x
       grind)
    | exact resolve eq7210 eq59414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7210 eq59414
  have eq120286 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ x) y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq98084 eq119931
    | (have j0 := eq119931 x (M.op x y)
       grind)
    | exact resolve eq119931 eq98084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98084 eq119931
  have eq120721 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ x) y) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq120286
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq120286
    | exact resolve eq120286 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120286
  have eq121015 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq44560 eq120721
    | exact resolve eq120721 eq44560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44560 eq120721
  have eq121210 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq121015
    | exact resolve eq121015 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121015
  have eq121296 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq121210
    | exact resolve eq121210 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121210
  have eq240937 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq121296 eq98063
    | exact resolve eq98063 eq121296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98063 eq121296
  have eq240959 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq240937
  have eq240964 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq240959
       have r₂ := eq27
       grind)
    | exact resolve eq240959 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240959
  have eq240973 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = X0 ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq240964 eq13
    | (have j0 := eq13 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (σ (M.op x y))
       have r₂ := eq240964
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq240964
       grind)
    | exact resolve eq13 eq240964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240964
  have eq241065 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq240973 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240973
  have eq241854 : ∀ X0 X1 : G, (M.op x y) ≠ (M.op x y) ∨ (k X0 (M.op x y)) = X0 ∨ (k X1 (σ (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq241065 (M.op X1 X1)
       grind)
    | exact superpose eq241065 eq13
    | (have j0 := eq13 X0 (M.op x y)
       have j1 := eq241065 X1
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq241065 X0
       grind)
    | exact resolve eq13 eq241065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241065
  have eq241944 : ∀ X0 X1 : G, (k X1 (σ (M.op x y))) = X1 ∨ (k X0 (M.op x y)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq241854 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241854
  have eq243191 : ∀ X0 : G, (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq142
       have i₂ := eq241944 (k sF1 sF1) x
       grind)
    | exact superpose eq241944 eq142
    | (have j1 := eq241944 X0 x
       grind)
    | exact resolve eq142 eq241944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq241944
  have eq243663 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq30 eq243191
    | (have j0 := eq243191 (M.op x y)
       grind)
    | exact resolve eq243191 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq243191
  have eq243822 : ∀ X0 : G, (k X0 (M.op x y)) = X0 := by
    intro X0
    first
    | (have j0 := eq243663 X0
       have j1 := eq12425 (M.op x y) X0
       grind)
    | (have r₁ := eq243663 X0
       have r₂ := eq12425 (M.op x y) x
       grind)
    | (have r₁ := eq243663 (M.op x y)
       have r₂ := eq12425 (M.op x y) x
       grind)
    | exact resolve eq243663 eq12425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12425 eq243663
  have eq244002 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq243822 eq105
    | (have j0 := eq105 (M.op x y)
       grind)
    | exact resolve eq105 eq243822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq244004 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq243822 eq3396
    | (have j0 := eq3396 (M.op x y)
       grind)
    | exact resolve eq3396 eq243822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3396 eq243822
  have eq244214 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq244004
  have eq244215 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq244002
  have eq244388 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq244214
    | exact resolve eq244214 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244214
  have eq244896 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq244215 eq340
    | exact resolve eq340 eq244215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq244913 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq47053 eq244896
    | exact resolve eq244896 eq47053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47053 eq244896
  have eq244966 : x = (M.op x y) := by
    first
    | exact superpose eq244215 eq244913
    | exact resolve eq244913 eq244215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244215 eq244913
  have eq244992 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq244966 eq20
    | exact resolve eq20 eq244966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq244966
  have eq245415 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq244992
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq244992
    | exact resolve eq244992 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq244992
  have eq246941 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq244388 eq60
    | exact resolve eq60 eq244388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq246947 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq244388 eq196
    | exact resolve eq196 eq244388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq247075 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq245415 eq246947
    | exact resolve eq246947 eq245415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246947
  have eq247079 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq44060 eq246941
    | exact resolve eq246941 eq44060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44060 eq246941
  have eq247105 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq244388 eq247075
    | exact resolve eq247075 eq244388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244388 eq247075
  have eq247108 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq245415 eq247079
    | exact resolve eq247079 eq245415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245415 eq247079
  have eq249283 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq247108 eq357
    | exact resolve eq357 eq247108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq249294 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq247108 eq249283
    | exact resolve eq249283 eq247108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247108 eq249283
  have eq249305 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq247105 eq249294
    | exact resolve eq249294 eq247105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247105 eq249294
  have eq249314 : False := by grind
  exact eq249314

/-- `Equation1845`: `x = (x ◇ (x ◇ y)) ◇ (z ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_y_pxx_y_pxy_Equation1845 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law1845 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1845.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ b ∨ k a b = b :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op X2 X2)) = X0 := by
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
  clear eq41
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
  have eq174 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
       have i₂ := eq16 X0 X1 (M.op X0 (M.op X0 X1))
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq539 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 (M.op X0 X1)) (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq177 (M.op X0 (M.op X0 X1)) (M.op x x) X3
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq546 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X3 X3)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq177 X0 x X3
       have i₂ := eq177 X0 x X1
       grind)
    | (have i₁ := eq177 x x x
       have i₂ := eq177 x X1 x
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X1 x
       have i₂ := eq177 X0 X2 x
       grind)
    | (have i₁ := eq177 X1 X1 X1
       have i₂ := eq177 X1 X1 X2
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X3 X3)) = X0 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X0 x X3
       have i₂ := eq177 X0 x X1
       grind)
    | (have i₁ := eq16 x x x
       have i₂ := eq177 x X1 x
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq569 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X0 X1)) (M.op (M.op X0 (M.op X0 X1)) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq177 (M.op X0 (M.op X0 X1)) X2 x
       grind)
    | (have i₁ := eq16 X0 X1 (M.op X0 (M.op X0 X1))
       have i₂ := eq177 (M.op X0 (M.op X0 X1)) (M.op X0 (M.op X0 X1)) X2
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | (have i₁ := eq175 (M.op sF2 sF4)
       have i₂ := eq177 (M.op sF2 sF4) (M.op sF2 sF4) x
       grind)
    | (have i₁ := eq175 x
       have i₂ := eq177 (M.op sF2 sF4) x x
       grind)
    | exact superpose eq177 eq175
    | exact resolve eq175 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq576 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq539 X0 X1 x
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq539
    | exact resolve eq539 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539
  have eq595 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq576 X0 x
       have i₂ := eq177 X0 x X1
       grind)
    | (have i₁ := eq576 x x
       have i₂ := eq177 x X1 x
       grind)
    | exact superpose eq177 eq576
    | exact resolve eq576 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1038 : y ≠ (M.op x y) ∨ y = (M.op y y) ∨ y = (k x y) := by
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
  have eq1041 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1062 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
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
  have eq1065 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1069 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (k X0 X1)) (M.op X2 X2)) = X0 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq16
    | (have j1 := eq11 X0 X1
       grind)
    | exact resolve eq16 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1084 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1091 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (k X0 X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq180 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq180
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq180 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1126 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1127 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1128 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1127 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq1134 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1091 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091
  have eq1141 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1084 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1084
  have eq1162 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1141 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq1141 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq1141 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq1177 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1062
       grind)
    | exact superpose eq1062 eq40
    | exact resolve eq40 eq1062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1178 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1177
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1177
    | exact resolve eq1177 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177
  have eq1180 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1178
    | exact resolve eq1178 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178
  have eq1244 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1180 eq1065
    | exact resolve eq1065 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq1251 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1244
       have r₂ := eq27
       grind)
    | exact resolve eq1244 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1244
  have eq1261 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq1251 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq1251
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1251
       grind)
    | exact resolve eq13 eq1251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1275 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq1261 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq1444 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1251
       have i₂ := eq1275 sF3
       grind)
    | exact superpose eq1275 eq1251
    | exact resolve eq1251 eq1275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1275
  have eq1446 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq1444
  have eq1488 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1446 eq152
    | exact resolve eq152 eq1446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1446
  have eq1493 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31 eq1488
    | exact resolve eq1488 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq1496 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1128 y
       grind)
    | (have r₁ := eq1493
       have r₂ := eq1128 y
       grind)
    | exact resolve eq1493 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493
  have eq1501 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq1496
       grind)
    | exact superpose eq1496 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq1496
       grind)
    | exact resolve eq13 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1502 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X1)) y) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 y
       have i₂ := eq1496
       grind)
    | exact superpose eq1496 eq16
    | exact resolve eq16 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1503 : x = (M.op (M.op x (M.op x y)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq1496
       grind)
    | exact superpose eq1496 eq174
    | exact resolve eq174 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1504 : (σ x) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq175 y
       have i₂ := eq1496
       grind)
    | exact superpose eq1496 eq175
    | exact resolve eq175 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1505 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq177 X0 X1 y
       have i₂ := eq1496
       grind)
    | exact superpose eq1496 eq177
    | exact resolve eq177 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1506 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq178 y
       have i₂ := eq1496
       grind)
    | exact superpose eq1496 eq178
    | exact resolve eq178 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1508 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq180 y
       have i₂ := eq1496
       grind)
    | exact superpose eq1496 eq180
    | exact resolve eq180 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1511 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1 y
       have i₂ := eq1496
       grind)
    | exact superpose eq1496 eq546
    | exact resolve eq546 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1514 : ∀ X0 : G, (M.op (M.op X0 y) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq595 X0 y
       have i₂ := eq1496
       grind)
    | exact superpose eq1496 eq595
    | exact resolve eq595 eq1496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1520 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1501 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1501
  have eq1530 : (M.op x y) = (M.op x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1506
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1506
    | exact resolve eq1506 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1506
  have eq1531 : (σ x) = (M.op (M.op (σ x) y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1508 eq1504
    | exact resolve eq1504 eq1508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1504
  have eq1532 : ∀ X0 : G, (M.op (M.op X0 y) y) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1505 eq1502
    | exact resolve eq1502 eq1505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1502
  have eq1537 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1530 eq174
    | exact resolve eq174 eq1530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1544 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1530 eq12
    | (have j0 := eq12 x (M.op x y)
       grind)
    | (have r₁ := eq12 x (M.op x y)
       have r₂ := eq1530
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1530
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1530
       grind)
    | exact resolve eq12 eq1530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1550 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1544
  have eq1553 : ∀ X0 : G, x = (M.op (M.op x y) (k X0 y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1520 eq1537
    | exact resolve eq1537 eq1520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1537
  have eq1572 : x = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1530 eq1503
    | exact resolve eq1503 eq1530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1503
  have eq1583 : x = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1572
  have eq1639 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (k (M.op X0 y) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq12 (M.op X0 y) X0
       have i₂ := eq1514 X0
       grind)
    | exact superpose eq1514 eq12
    | (have j0 := eq12 (M.op X0 y) X0
       grind)
    | (have r₁ := eq12 (M.op X0 y) X0
       have r₂ := eq1514 X0
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq1514 X0
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq1514 X0
       grind)
    | exact resolve eq12 eq1514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1514
  have eq1651 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (M.op X0 y) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1639 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1639
  have eq1663 : ∀ X0 : G, (k (M.op X0 y) X0) = X0 ∨ (k X0 y) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1520 eq1651
    | (have j0 := eq1651 X0
       grind)
    | exact resolve eq1651 eq1520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1651
  have eq1668 : ∀ X0 : G, (k X0 y) = (k X0 X0) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1520 X0
       have i₂ := eq11 X0 X0
       grind)
    | exact superpose eq11 eq1520
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq1520 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1673 : ∀ X0 X1 : G, (k X0 y) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq1520 X0
       grind)
    | exact superpose eq1520 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq1520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1701 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op X0 X0)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq560 (M.op X0 X0) X0 (M.op X0 X0)
       have i₂ := eq1520 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq1520 eq560
    | exact resolve eq560 eq1520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1705 : y = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1496
       have i₂ := eq1520 y
       grind)
    | exact superpose eq1520 eq1496
    | exact resolve eq1496 eq1520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1709 : y = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1705
  have eq1717 : ∀ X0 : G, (k X0 y) = (k X0 X0) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1668 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1668
  have eq1722 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1511 eq1701
    | exact resolve eq1701 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1701
  have eq1747 : ∀ X0 : G, (k X0 y) = (k (M.op (k X0 y) y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f1747_14 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f1747_15 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f1747_24 : (k X0 y) ≠ (k (M.op (k X0 y) y) y) := by grind
    have f1747_25 : y ≠ (M.op x y) := by grind
    have f1747_26 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f1747_27 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      first
      | (have j0 := f1747_15 X0
         grind)
      | (have r₁ := f1747_15 X0
         have r₂ := f1747_25
         grind)
      | exact resolve f1747_15 f1747_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1747_28 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) y) y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      first
      | (have j0 := f1747_14 X0
         grind)
      | (have r₁ := f1747_14 X0
         have r₂ := f1747_25
         grind)
      | exact resolve f1747_14 f1747_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1747_29 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) := by
      intro X0
      first
      | (have j0 := f1747_27 X0
         grind)
      | (have r₁ := f1747_27 X0
         have r₂ := f1747_26
         grind)
      | exact resolve f1747_27 f1747_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1747_30 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) y) y) := by
      intro X0
      first
      | (have j0 := f1747_28 X0
         grind)
      | (have r₁ := f1747_28 X0
         have r₂ := f1747_26
         grind)
      | exact resolve f1747_28 f1747_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1747_41 : (M.op X0 X0) ≠ (k (M.op (M.op X0 X0) y) y) := by
      first
      | (have i₁ := f1747_24
         have i₂ := f1747_29 X0
         grind)
      | exact superpose f1747_29 f1747_24
      | exact resolve f1747_24 f1747_29
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1747_42 : False := by
      first
      | (have r₁ := f1747_41
         have r₂ := f1747_30 X0
         grind)
      | exact resolve f1747_41 f1747_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f1747_42
  clear eq1722
  have eq1759 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1126 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq1126
    | (have j0 := eq1126 (σ X0) (σ X1)
       grind)
    | exact resolve eq1126 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1878 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq1709
       grind)
    | exact superpose eq1709 eq40
    | exact resolve eq40 eq1709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1709
  have eq1887 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1878
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1878
    | exact resolve eq1878 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1878
  have eq1893 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1887 eq1162
    | (have j0 := eq1162 (σ y) X0
       grind)
    | (have r₁ := eq1162 (σ y) x
       have r₂ := eq1887
       grind)
    | exact resolve eq1162 eq1887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq1895 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1887 eq1126
    | (have j0 := eq1126 (σ y) (σ y)
       grind)
    | (have r₁ := eq1126 (σ y) (σ y)
       have r₂ := eq1887
       grind)
    | exact resolve eq1126 eq1887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1887
  have eq1896 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1895
  have eq1897 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1896
  have eq1899 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq1893 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1893
  have eq1909 : x = (M.op (M.op x (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1897 eq174
    | exact resolve eq174 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1911 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1897 eq177
    | exact resolve eq177 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1914 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1897 eq180
    | exact resolve eq180 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1917 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1897 eq546
    | exact resolve eq546 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1919 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (σ y)) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1897 eq560
    | exact resolve eq560 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1942 : ∀ X0 : G, (M.op (M.op X0 y) (σ y)) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1511 eq1919
    | exact resolve eq1919 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1919
  have eq1944 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X0 (k X1 y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq1520 eq1917
    | exact resolve eq1917 eq1520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1917
  have eq1947 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq1914
    | exact resolve eq1914 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1914
  have eq1951 : x = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1530 eq1909
    | exact resolve eq1909 eq1530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1909
  have eq1970 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1947 eq175
    | exact resolve eq175 eq1947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1972 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1947 eq571
    | exact resolve eq571 eq1947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1976 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1947 eq1508
    | exact resolve eq1508 eq1947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1508 eq1947
  have eq1986 : (M.op (σ x) (σ y)) = (M.op (σ x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq1976
  have eq1990 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (k X0 y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1520 eq1970
    | exact resolve eq1970 eq1520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1970
  have eq2117 : (σ x) = (M.op (M.op (σ x) (σ y)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1986 eq1531
    | exact resolve eq1531 eq1986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1531
  have eq2130 : (σ x) = (M.op (M.op (σ x) (σ y)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2117
  have eq2348 : ∀ X0 X1 : G, (k X0 (σ y)) ≠ X0 ∨ (M.op X1 X1) = (k X1 X0) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq1899 X0
       grind)
    | exact superpose eq1899 eq13
    | (have j0 := eq13 X1 X0
       grind)
    | exact resolve eq13 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2350 : ∀ X0 : G, x = (M.op (M.op x (M.op x y)) (k X0 (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq174 X0
       have i₂ := eq1899 X0
       grind)
    | exact superpose eq1899 eq174
    | exact resolve eq174 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2362 : ∀ X0 : G, (k X0 y) = (k X0 (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1520 X0
       have i₂ := eq1899 X0
       grind)
    | exact superpose eq1899 eq1520
    | exact resolve eq1520 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2378 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) (M.op X0 X0)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq560 (M.op X0 X0) X0 (M.op X0 X0)
       have i₂ := eq1899 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact superpose eq1899 eq560
    | exact resolve eq560 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2382 : y = (k y (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1496
       have i₂ := eq1899 y
       grind)
    | exact superpose eq1899 eq1496
    | exact resolve eq1496 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496
  have eq2392 : y = (k y (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2382
  have eq2397 : ∀ X0 : G, (k X0 y) = (k X0 (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2362 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2362
  have eq2407 : ∀ X0 : G, (M.op X0 X0) = (k (M.op (M.op X0 X0) y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1511 eq2378
    | exact resolve eq2378 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2378
  have eq2429 : ∀ X0 : G, x = (M.op (M.op x y) (k X0 (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1530 eq2350
    | exact resolve eq2350 eq1530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1530 eq2350
  have eq2436 : ∀ X0 : G, (k X0 y) = (k (M.op (k X0 y) y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1520 eq2407
    | exact resolve eq2407 eq1520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2407
  have eq2449 : ∀ X0 : G, (k X0 (σ y)) = (k (M.op (k X0 (σ y)) y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2397 eq2436
    | exact resolve eq2436 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2436
  have eq2466 : (τ y) = (k (τ y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2392 eq152
    | exact resolve eq152 eq2392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2392
  have eq2561 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1942 (M.op X0 y)
       have i₂ := eq1532 X0
       grind)
    | exact superpose eq1532 eq1942
    | exact resolve eq1942 eq1532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1532
  have eq2568 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1986 eq1942
    | exact resolve eq1942 eq1986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2584 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2568
  have eq2588 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq2561 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2561
  have eq2984 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op (k X0 X1) (k X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (M.op (k X0 (k X0 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1069 X0 X1 X2
       have i₂ := eq11 X0 (k X0 X1)
       grind)
    | exact superpose eq11 eq1069
    | (have j0 := eq1069 (k X0 X1) (k X0 X1) X2
       have j1 := eq11 (k X0 X1) (k X0 X1)
       grind)
    | exact resolve eq1069 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq3101 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq2397 X0
       grind)
    | exact superpose eq2397 eq40
    | exact resolve eq40 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3107 : ∀ X0 : G, (τ (k (σ X0) (σ y))) = (k X0 (τ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq366 X0 y
       have i₂ := eq2397 (σ X0)
       grind)
    | exact superpose eq2397 eq366
    | exact resolve eq366 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq3135 : ∀ X0 : G, (k X0 y) = (k X0 (τ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq72 eq3107
    | exact resolve eq3107 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3107
  have eq3144 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (τ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2397 eq3135
    | exact resolve eq3135 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3135
  have eq3829 : (τ y) = (k (τ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2397 (τ y)
       have i₂ := eq2466
       grind)
    | exact superpose eq2466 eq2397
    | exact resolve eq2397 eq2466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2466
  have eq3832 : (τ y) = (k (τ y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3829
  have eq4926 : (τ y) ≠ (k (τ y) (σ y)) ∨ (τ y) = (M.op (τ y) (τ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1128 (τ y)
       have i₂ := eq3144 (τ y)
       grind)
    | exact superpose eq3144 eq1128
    | (have j0 := eq1128 (τ y)
       grind)
    | exact resolve eq1128 eq3144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3144
  have eq4951 : (τ y) = (M.op (τ y) (τ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq4926
       have r₂ := eq3832
       grind)
    | exact resolve eq4926 eq3832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3832 eq4926
  have eq5250 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X1 X1)) (τ y)) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq560 X0 X1 (τ y)
       have i₂ := eq4951
       grind)
    | exact superpose eq4951 eq560
    | exact resolve eq560 eq4951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq5251 : ∀ X0 : G, (M.op (M.op X0 (τ y)) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq595 X0 (τ y)
       have i₂ := eq4951
       grind)
    | exact superpose eq4951 eq595
    | exact resolve eq595 eq4951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq595 eq4951
  have eq5286 : ∀ X0 : G, (M.op (M.op X0 y) (τ y)) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1511 eq5250
    | exact resolve eq5250 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5250
  have eq5309 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (τ y)) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2588 eq5286
    | exact resolve eq5286 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5286
  have eq6946 : ∀ X0 : G, (k (M.op X0 X0) (σ y)) = (M.op (M.op X0 X0) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1899 (M.op X0 X0)
       have i₂ := eq1511 (M.op X0 X0) X0
       grind)
    | exact superpose eq1511 eq1899
    | exact resolve eq1899 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7008 : ∀ X0 : G, (k (M.op X0 X0) (σ y)) = (M.op (M.op X0 X0) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq6946 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6946
  have eq7049 : ∀ X0 : G, (M.op (k X0 y) y) = (k (k X0 y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1520 eq7008
    | exact resolve eq7008 eq1520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7008
  have eq7102 : ∀ X0 : G, (k (k X0 (σ y)) (σ y)) = (M.op (k X0 (σ y)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2397 eq7049
    | exact resolve eq7049 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7049
  have eq9537 : ∀ X0 : G, (k (k X0 y) (σ y)) = (M.op (k X0 y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1899 (k X0 y)
       have i₂ := eq1944 (k X0 y) X0
       grind)
    | exact superpose eq1944 eq1899
    | exact resolve eq1899 eq1944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9601 : ∀ X0 : G, (k (k X0 y) (σ y)) = (M.op (k X0 y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq9537 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9537
  have eq9646 : ∀ X0 : G, (k (k X0 (σ y)) (σ y)) = (M.op (k X0 (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2397 eq9601
    | exact resolve eq9601 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9601
  have eq16717 : ∀ X0 : G, (k X0 (σ y)) = (M.op (k (k X0 (σ y)) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq7102 eq1942
    | exact resolve eq1942 eq7102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1942 eq7102
  have eq16737 : ∀ X0 : G, (k X0 (σ y)) = (M.op (k (k X0 (σ y)) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq16717 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16717
  have eq17323 : ∀ X0 : G, (k X0 (σ y)) = (M.op (k (k X0 (σ y)) (σ y)) (τ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq9646 eq5309
    | exact resolve eq5309 eq9646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5309
  have eq17346 : ∀ X0 : G, (k X0 (σ y)) = (M.op (k (k X0 (σ y)) (σ y)) (τ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq17323 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17323
  have eq22701 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1583 eq1663
    | (have j0 := eq1663 (M.op x y)
       grind)
    | exact resolve eq1663 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22704 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2130 eq1663
    | (have j0 := eq1663 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1663 eq2130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1663 eq2130
  have eq22850 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) y) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22704
  have eq22853 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq22701
  have eq22896 : (M.op x y) = (k (M.op x y) (σ y)) ∨ (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2397 eq22853
    | exact resolve eq22853 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22853
  have eq22978 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22896 eq2429
    | exact resolve eq2429 eq22896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2429
  have eq22979 : (M.op x y) = (k (M.op (M.op x y) y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22896 eq2449
    | exact resolve eq2449 eq22896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2449 eq22896
  have eq23034 : (M.op x y) = (k (M.op (M.op x y) y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x (M.op x y)) := by grind
  clear eq22979
  have eq23035 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x (M.op x y)) := by grind
  clear eq22978
  have eq23061 : (M.op x y) = (k x (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq1583 eq23034
    | exact resolve eq23034 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23034
  have eq23062 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1550 eq23035
    | exact resolve eq23035 eq1550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1550 eq23035
  have eq24148 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22850 eq2397
    | exact resolve eq2397 eq22850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22850
  have eq24151 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq24148
  have eq24794 : (M.op (σ x) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq24151 eq16737
    | exact resolve eq16737 eq24151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16737
  have eq24797 : (M.op (σ x) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq24794
  have eq24834 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq24151 eq24797
    | exact resolve eq24797 eq24151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24797
  have eq24854 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2584 eq24834
    | exact resolve eq24834 eq2584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2584 eq24834
  have eq27403 : ∀ X0 : G, x ≠ (M.op x y) ∨ (M.op X0 X0) = (k X0 x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq23061 eq2348
    | (have j0 := eq2348 x X0
       grind)
    | exact resolve eq2348 eq23061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2348
  have eq27432 : ∀ X0 : G, x ≠ (M.op x y) ∨ (M.op X0 X0) = (k X0 x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq27403 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27403
  have eq27450 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq27432 X0
       grind)
    | (have r₁ := eq27432 X0
       have r₂ := eq23062
       grind)
    | exact resolve eq27432 eq23062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27432
  have eq27461 : ∀ X0 : G, (k X0 x) = (k X0 (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1899 eq27450
    | exact resolve eq27450 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27450
  have eq27469 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    intro X0
    first
    | exact superpose eq23062 eq27461
    | exact resolve eq27461 eq23062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23062 eq27461
  have eq34476 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq27469 eq23061
    | exact resolve eq23061 eq27469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23061 eq27469
  have eq34520 : (M.op x y) = (k x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq34476
  have eq34630 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34520 eq35
    | exact resolve eq35 eq34520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq34520
  have eq34636 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq34630
    | exact resolve eq34630 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34630
  have eq34642 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34636 eq1126
    | (have j0 := eq1126 (σ x) (σ (M.op x y))
       grind)
    | (have r₁ := eq1126 (σ x) (σ (M.op x y))
       have r₂ := eq34636
       grind)
    | exact resolve eq1126 eq34636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126 eq34636
  have eq34643 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq34642
  have eq34715 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34643 eq1911
    | exact resolve eq1911 eq34643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1911
  have eq34716 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq34715
  have eq34726 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq34716
    | exact resolve eq34716 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34716
  have eq34740 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq34643 eq34726
    | exact resolve eq34726 eq34643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34643 eq34726
  have eq34752 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq34740
       have r₂ := eq27
       grind)
    | exact resolve eq34740 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34740
  have eq34775 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 X0) = (k X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq34752 eq13
    | (have j0 := eq13 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq13 X0 (σ (M.op x y))
       have r₂ := eq34752
       grind)
    | exact resolve eq13 eq34752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34796 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq34752 eq1511
    | exact resolve eq1511 eq34752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511
  have eq34800 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq34752 eq1899
    | exact resolve eq1899 eq34752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34807 : ∀ X0 : G, (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq34752 eq569
    | exact resolve eq569 eq34752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34752
  have eq34819 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq34800
  have eq34823 : ∀ X0 : G, (M.op X0 y) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq34796 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34796
  have eq34825 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq34775 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34775
  have eq34837 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ (M.op x y)) y) (M.op (k (σ (M.op x y)) y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1520 eq34807
    | exact resolve eq34807 eq1520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34807
  have eq34844 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2588 eq34823
    | exact resolve eq34823 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34823
  have eq34860 : ∀ X0 : G, (k X0 y) = (k X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1520 eq34825
    | exact resolve eq34825 eq1520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34825
  have eq34867 : ∀ X0 : G, (σ (M.op x y)) = (M.op (k (σ (M.op x y)) (σ y)) (M.op (k (σ (M.op x y)) (σ y)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2397 eq34837
    | exact resolve eq34837 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34837
  have eq34885 : ∀ X0 : G, (k X0 (σ y)) = (k X0 (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2397 eq34860
    | exact resolve eq34860 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34860
  have eq34892 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq34819 eq34867
    | exact resolve eq34867 eq34819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34867
  have eq34925 : (τ (σ (M.op x y))) = (k (τ (σ (M.op x y))) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34819 eq152
    | exact resolve eq152 eq34819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34819
  have eq35034 : (M.op x y) = (k (M.op x y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq34925
    | exact resolve eq34925 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq34925
  have eq36462 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35034 eq1553
    | exact resolve eq1553 eq35034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1553
  have eq36464 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op X0 X0) = (k X0 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq35034 eq1673
    | (have j0 := eq1673 (M.op x y) X0
       grind)
    | (have r₁ := eq1673 (M.op x y) x
       have r₂ := eq35034
       grind)
    | exact resolve eq1673 eq35034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36467 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35034 eq1717
    | (have j0 := eq1717 (M.op x y)
       grind)
    | exact resolve eq1717 eq35034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1717
  have eq36473 : (M.op x y) = (k (M.op (M.op x y) y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35034 eq1747
    | exact resolve eq1747 eq35034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36475 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq35034 eq1944
    | exact resolve eq1944 eq35034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1944
  have eq36477 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35034 eq1990
    | exact resolve eq1990 eq35034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1990
  have eq36479 : (M.op x y) = (k (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq35034 eq2397
    | exact resolve eq2397 eq35034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35034
  have eq36482 : (M.op x y) = (k (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq36479
  have eq36484 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq36477
  have eq36486 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq36475 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36475
  have eq36488 : (M.op x y) = (k (M.op (M.op x y) y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq36473
  have eq36494 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq36467
  have eq36497 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ (M.op X0 X0) = (k X0 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq36464 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36464
  have eq36498 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq36497 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36497
  have eq36500 : x = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq36462
  have eq36508 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1583 eq36488
    | exact resolve eq36488 eq1583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1583 eq36488
  have eq36512 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq1128 (M.op x y)
       grind)
    | (have r₁ := eq36494
       have r₂ := eq1128 (M.op x y)
       grind)
    | exact resolve eq36494 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36494
  have eq36566 : (k (M.op x y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36482 eq9646
    | exact resolve eq9646 eq36482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9646
  have eq36591 : (k (M.op x y) (σ y)) = (M.op (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq36566
  have eq36637 : x = (k (M.op x y) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1951 eq36591
    | exact resolve eq36591 eq1951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951 eq36591
  have eq36653 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36482 eq36637
    | exact resolve eq36637 eq36482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36482 eq36637
  have eq36664 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq36653 eq571
    | exact resolve eq571 eq36653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36666 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36653 eq1041
    | (have r₁ := eq1041
       have r₂ := eq36653
       grind)
    | exact resolve eq1041 eq36653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36670 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq36666
  have eq36675 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq36664
    | (have j0 := eq36664 X0
       grind)
    | exact resolve eq36664 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36664
  have eq36681 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq36653 eq36675
    | exact resolve eq36675 eq36653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36675
  have eq37020 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq36508
       grind)
    | exact superpose eq36508 eq40
    | exact resolve eq40 eq36508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq37024 : ∀ X0 : G, x ≠ (M.op x y) ∨ (M.op X0 X0) = (k X0 x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1673 x X0
       have i₂ := eq36508
       grind)
    | exact superpose eq36508 eq1673
    | (have j0 := eq1673 x X0
       grind)
    | exact resolve eq1673 eq36508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673 eq36508
  have eq37059 : ∀ X0 : G, x ≠ (M.op x y) ∨ (M.op X0 X0) = (k X0 x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq37024 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37024
  have eq37072 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq37059 X0
       grind)
    | (have r₁ := eq37059 X0
       have r₂ := eq36653
       grind)
    | exact resolve eq37059 eq36653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37059
  have eq37073 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq37020
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37020
    | exact resolve eq37020 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37020
  have eq37079 : ∀ X0 : G, (k X0 x) = (k X0 (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq1899 eq37072
    | exact resolve eq37072 eq1899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1899 eq37072
  have eq37080 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq37073
    | exact resolve eq37073 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37073
  have eq37083 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq36653 eq37079
    | exact resolve eq37079 eq36653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37079
  have eq37101 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (M.op X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq36512 eq177
    | exact resolve eq177 eq36512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq36512
  have eq37776 : (k (σ (σ x)) (σ y)) = (σ (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37080 eq3101
    | exact resolve eq3101 eq37080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3101
  have eq37839 : (k (σ (σ x)) (σ y)) = (σ (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq37776
  have eq40611 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq34885 eq85
    | exact resolve eq85 eq34885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq34885
  have eq40689 : ∀ X0 : G, (k X0 y) = (k X0 (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq72 eq40611
    | exact resolve eq40611 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40611
  have eq42761 : ∀ X0 : G, (k X0 (M.op x y)) = (k (M.op (k X0 (M.op x y)) y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1747 X0
       have i₂ := eq40689 X0
       grind)
    | exact superpose eq40689 eq1747
    | exact resolve eq1747 eq40689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1747 eq40689
  have eq42864 : ∀ X0 : G, (k X0 (M.op x y)) = (k (M.op (k X0 (M.op x y)) y) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq42761 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42761
  have eq42927 : ∀ X0 : G, (k X0 (M.op x y)) = (k (M.op (k X0 (M.op x y)) (σ y)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq2588 eq42864
    | exact resolve eq42864 eq2588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2588 eq42864
  have eq42959 : ∀ X0 : G, (k X0 (M.op x y)) = (k (M.op (k X0 (M.op x y)) (M.op x y)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq36486 eq42927
    | exact resolve eq42927 eq36486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36486 eq42927
  have eq48245 : (σ (M.op x y)) = (k (σ x) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37083 eq37080
    | exact resolve eq37080 eq37083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48257 : (σ (M.op x y)) = (k (σ x) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq48245
  have eq50201 : (k (σ x) y) = (τ (σ (σ (M.op x y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq37839 eq72
    | exact resolve eq72 eq37839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq37839
  have eq50324 : (σ (M.op x y)) = (k (σ x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq50201
       have i₂ := eq15 sF1
       grind)
    | exact superpose eq15 eq50201
    | exact resolve eq50201 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50201
  have eq90052 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36670 eq90
    | exact resolve eq90 eq36670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36670
  have eq90186 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq90052
    | exact resolve eq90052 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90052
  have eq97587 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ y) (σ y)) X0)) ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq90186 eq569
    | exact resolve eq569 eq90186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97651 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (k x y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq90186 eq97587
    | exact resolve eq97587 eq90186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90186 eq97587
  have eq97670 : y = (k x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36681 eq97651
    | exact resolve eq97651 eq36681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97651
  have eq97705 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1062
       have i₂ := eq97670
       grind)
    | exact superpose eq97670 eq1062
    | exact resolve eq1062 eq97670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062 eq97670
  have eq97756 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq97705
  have eq97804 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq97756
       grind)
    | exact superpose eq97756 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq97756
       grind)
    | exact resolve eq13 eq97756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97876 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq97804 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97804
  have eq106458 : y = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq97756
       have i₂ := eq97876 y
       grind)
    | exact superpose eq97876 eq97756
    | exact resolve eq97756 eq97876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97756
  have eq106506 : y = (k y y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq106458
  have eq106897 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1759 y y
       have i₂ := eq106506
       grind)
    | exact superpose eq106506 eq1759
    | (have j0 := eq1759 y y
       grind)
    | exact resolve eq1759 eq106506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106506
  have eq106908 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq106897
  have eq106909 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq106908
  have eq106951 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq106909
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq106909
    | exact resolve eq106909 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106909
  have eq107032 : (σ y) = (k (σ y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq106951 eq97876
    | exact resolve eq97876 eq106951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107038 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ y) (σ y)) X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq106951 eq569
    | exact resolve eq569 eq106951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106951
  have eq107059 : (σ y) = (k (σ y) y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq107032
  have eq107109 : ∀ X0 : G, (σ y) = (M.op (k (σ y) y) (M.op (k (σ y) y) X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq97876 eq107038
    | exact resolve eq107038 eq97876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97876 eq107038
  have eq107138 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq107059 eq107109
    | exact resolve eq107109 eq107059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107059 eq107109
  have eq107153 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq36681 eq107138
    | exact resolve eq107138 eq36681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36681 eq107138
  have eq107154 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq107153
  have eq107165 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq107154 eq31
    | exact resolve eq31 eq107154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108109 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq107165
    | exact resolve eq107165 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107165
  have eq110584 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq108109
       grind)
    | exact superpose eq108109 eq24
    | exact resolve eq24 eq108109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110587 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k x (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1038
       have i₂ := eq108109
       grind)
    | exact superpose eq108109 eq1038
    | (have r₁ := eq1038
       have r₂ := eq108109
       grind)
    | exact resolve eq1038 eq108109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108109
  have eq110589 : (M.op x y) = (k x (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq110587
  have eq110592 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq110584
    | exact resolve eq110584 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110584
  have eq143839 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq110589 eq1759
    | (have j0 := eq1759 x (M.op x y)
       grind)
    | exact resolve eq1759 eq110589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110589
  have eq143855 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq143839
  have eq143862 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq143855
    | exact resolve eq143855 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143855
  have eq143866 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq143862
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq143862
    | exact resolve eq143862 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143862
  have eq143870 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq143866
    | exact resolve eq143866 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143866
  have eq143873 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq110592 eq143870
    | exact resolve eq143870 eq110592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143870
  have eq143875 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq110592 eq143873
    | exact resolve eq143873 eq110592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143873
  have eq143877 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq143875
    | exact resolve eq143875 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143875
  have eq143879 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1897 eq143877
    | exact resolve eq143877 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143877
  have eq143880 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq143879
  have eq193829 : (M.op (σ x) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (σ y)) (τ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq24151 eq17346
    | exact resolve eq17346 eq24151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17346 eq24151
  have eq193884 : (M.op (σ x) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (σ y)) (τ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq193829
  have eq193957 : (M.op (σ x) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (M.op x y)) (τ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq37083 eq193884
    | exact resolve eq193884 eq37083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193884
  have eq194003 : (σ x) = (M.op (k (σ x) (M.op x y)) (τ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq24854 eq193957
    | exact resolve eq193957 eq24854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24854 eq193957
  have eq194028 : (σ x) = (M.op (σ (M.op x y)) (τ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq48257 eq194003
    | exact resolve eq194003 eq48257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194003
  have eq194082 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq194028 eq5251
    | exact resolve eq5251 eq194028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5251 eq194028
  have eq194114 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq194082
  have eq194269 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq194114 eq90
    | exact resolve eq90 eq194114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194114
  have eq194287 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34844 eq194269
    | exact resolve eq194269 eq34844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34844 eq194269
  have eq194290 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq194287
    | exact resolve eq194287 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194287
  have eq194293 : (τ (M.op (σ x) (σ y))) = (k x (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq194290
       have r₂ := eq27
       grind)
    | exact resolve eq194290 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194290
  have eq194296 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36653 eq194293
    | exact resolve eq194293 eq36653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36653 eq194293
  have eq194316 : (σ (τ (M.op (σ x) (σ y)))) ≠ (σ (τ (M.op (σ x) (σ y)))) ∨ (σ (τ (M.op (σ x) (σ y)))) = (M.op (σ (M.op x y)) (σ (τ (M.op (σ x) (σ y))))) ∨ (σ (τ (M.op (σ x) (σ y)))) = (M.op (σ (τ (M.op (σ x) (σ y)))) (σ (τ (M.op (σ x) (σ y))))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq194296 eq1759
    | (have j0 := eq1759 (M.op x y) (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq1759 eq194296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194296
  have eq194326 : (σ (τ (M.op (σ x) (σ y)))) = (M.op (σ (M.op x y)) (σ (τ (M.op (σ x) (σ y))))) ∨ (σ (τ (M.op (σ x) (σ y)))) = (M.op (σ (τ (M.op (σ x) (σ y)))) (σ (τ (M.op (σ x) (σ y))))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq194316
  have eq194337 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (τ (M.op (σ x) (σ y)))) = (M.op (σ (τ (M.op (σ x) (σ y)))) (σ (τ (M.op (σ x) (σ y))))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq194326
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq194326
    | exact resolve eq194326 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194326
  have eq194344 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ (τ (M.op (σ x) (σ y)))) = (M.op (σ (τ (M.op (σ x) (σ y)))) (σ (τ (M.op (σ x) (σ y))))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq194337
    | exact resolve eq194337 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194337
  have eq194350 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq194344
       have i₂ := eq14 sF4
       grind)
    | exact superpose eq14 eq194344
    | exact resolve eq194344 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194344
  have eq194457 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq194350 eq36498
    | exact resolve eq36498 eq194350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36498
  have eq194482 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq194350 eq569
    | exact resolve eq569 eq194350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq194499 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq194350 eq37101
    | exact resolve eq37101 eq194350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37101
  have eq194502 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by grind
  clear eq194499
  have eq194520 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by grind
  clear eq194457
  have eq194541 : (k (M.op (σ x) (σ y)) y) = (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1520 eq194502
    | exact resolve eq194502 eq1520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194502
  have eq194552 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq194350 eq194482
    | exact resolve eq194482 eq194350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194350 eq194482
  have eq194581 : (k (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2397 eq194541
    | exact resolve eq194541 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194541
  have eq194591 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1972 eq194552
    | exact resolve eq194552 eq1972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1972 eq194552
  have eq194617 : (σ x) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq36484 eq194581
    | exact resolve eq194581 eq36484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194581
  have eq194646 : (σ x) = (k (M.op (σ x) (σ y)) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq37083 eq194617
    | exact resolve eq194617 eq37083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37083 eq194617
  have eq194668 : (σ x) = (k (σ x) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq194591 eq194646
    | exact resolve eq194646 eq194591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194646
  have eq194679 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq48257 eq194668
    | exact resolve eq194668 eq48257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48257 eq194668
  have eq194711 : ∀ X0 : G, (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq194591 eq554
    | exact resolve eq554 eq194591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554
  have eq194749 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq194591 eq194711
    | exact resolve eq194711 eq194591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194591 eq194711
  have eq194765 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34892 eq194749
    | exact resolve eq194749 eq34892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194749
  have eq194776 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq194765
       have r₂ := eq27
       grind)
    | exact resolve eq194765 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194765
  have eq195195 : (σ x) ≠ (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  have eq196163 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq194679 eq34892
    | exact resolve eq34892 eq194679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34892 eq194679
  have eq196194 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq196163
  have eq196216 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq194776 eq196194
    | exact resolve eq196194 eq194776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196194
  have eq197087 : (M.op (σ x) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (M.op x y)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq194520 eq42959
    | exact resolve eq42959 eq194520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42959 eq194520
  have eq197148 : (M.op (σ x) (σ y)) = (k (M.op (M.op (σ x) (σ y)) (M.op x y)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by grind
  clear eq197087
  have eq197189 : (M.op (σ x) (σ y)) = (k (σ x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq36484 eq197148
    | exact resolve eq197148 eq36484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36484 eq197148
  have eq197222 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2397 eq197189
    | exact resolve eq197189 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2397 eq197189
  have eq197241 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq37080 eq197222
    | exact resolve eq197222 eq37080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37080 eq197222
  have eq197249 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq197241
       have r₂ := eq27
       grind)
    | exact resolve eq197241 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197241
  have eq197253 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq194776 eq197249
    | exact resolve eq197249 eq194776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194776 eq197249
  have eq197261 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq197253 eq196216
    | exact resolve eq196216 eq197253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196216
  have eq197286 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ x)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq197253 eq576
    | exact resolve eq576 eq197253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq576
  have eq197326 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq197261
  have eq197339 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq197253 eq197286
    | exact resolve eq197286 eq197253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197253 eq197286
  have eq197359 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq197326 eq197339
    | exact resolve eq197339 eq197326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197326 eq197339
  have eq197546 : (M.op (σ x) (σ x)) = (M.op (σ x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq197359 eq1505
    | exact resolve eq1505 eq197359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1505 eq197359
  have eq197566 : (M.op (σ x) (σ x)) = (M.op (σ x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq197546
  have eq197616 : (M.op (σ x) y) = (k (σ x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1520 eq197566
    | exact resolve eq197566 eq1520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1520 eq197566
  have eq197654 : (M.op (σ x) (σ y)) = (k (σ x) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1986 eq197616
    | exact resolve eq197616 eq1986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1986 eq197616
  have eq197685 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq50324 eq197654
    | exact resolve eq197654 eq50324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50324 eq197654
  have eq197711 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq197685
       have r₂ := eq27
       grind)
    | exact resolve eq197685 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197685
  have eq197735 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq197711 eq27
    | exact resolve eq27 eq197711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197736 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq197711 eq175
    | exact resolve eq175 eq197711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq197738 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq197711 eq571
    | exact resolve eq571 eq197711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq197740 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq197711 eq1041
    | (have r₁ := eq1041
       have r₂ := eq197711
       grind)
    | exact resolve eq1041 eq197711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq197746 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq197740
  have eq197752 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq197738
    | (have j0 := eq197738 X0
       grind)
    | exact resolve eq197738 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197738
  have eq197754 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq197736
    | (have j0 := eq197736 X0
       grind)
    | exact resolve eq197736 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197736
  have eq197758 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq197711 eq197752
    | exact resolve eq197752 eq197711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197752
  have eq197760 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op X0 X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq197711 eq197754
    | exact resolve eq197754 eq197711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197754
  have eq202410 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq197746 eq1180
    | exact resolve eq1180 eq197746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202418 : (τ (σ y)) = (k x (τ (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq197746 eq90
    | exact resolve eq90 eq197746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq197746
  have eq202543 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq202410
  have eq202571 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq202418
    | exact resolve eq202418 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202418
  have eq202574 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq202543
       have r₂ := eq197735
       grind)
    | exact resolve eq202543 eq197735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197735 eq202543
  have eq202711 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq202571 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq202571
       grind)
    | exact resolve eq13 eq202571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202785 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ y) (σ y)) X0)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq202571 eq569
    | exact resolve eq569 eq202571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq202834 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq202711 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202711
  have eq202883 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (k x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq202571 eq202785
    | exact resolve eq202785 eq202571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202571 eq202785
  have eq202914 : (σ x) = (σ y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq197758 eq202883
    | exact resolve eq202883 eq197758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202883
  have eq202932 : y = (k (M.op x y) y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq107154 eq202914
    | exact resolve eq202914 eq107154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202914
  have eq203291 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq202574 eq197760
    | exact resolve eq197760 eq202574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197760
  have eq203297 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (M.op (σ y) (σ y)) X0)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq202574 eq569
    | exact resolve eq569 eq202574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq203326 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by grind
  clear eq203291
  have eq203395 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) X0)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq202574 eq203297
    | exact resolve eq203297 eq202574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203297
  have eq203430 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq197758 eq203395
    | exact resolve eq203395 eq197758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197758 eq203395
  have eq203494 : ∀ X0 : G, y ≠ y ∨ (M.op X0 X0) = (k X0 y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq203430
       grind)
    | exact superpose eq203430 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq203430
       grind)
    | exact resolve eq13 eq203430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203496 : x = (M.op (M.op x (M.op x y)) y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq174 y
       have i₂ := eq203430
       grind)
    | exact superpose eq203430 eq174
    | exact resolve eq174 eq203430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203613 : ∀ X0 : G, (M.op X0 X0) = (k X0 y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq203494 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203494
  have eq203666 : (M.op x y) = (M.op (M.op (M.op x y) (M.op x y)) y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq107154 eq203496
    | exact resolve eq203496 eq107154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107154 eq203496
  have eq203686 : (M.op x y) = (M.op (k (M.op x y) y) y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq203613 eq203666
    | exact resolve eq203666 eq203613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203613 eq203666
  have eq203696 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq202932 eq203686
    | exact resolve eq203686 eq202932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202932 eq203686
  have eq204243 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq203430
       have i₂ := eq203696
       grind)
    | exact superpose eq203696 eq203430
    | exact resolve eq203430 eq203696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203430 eq203696
  have eq204398 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq204243
  have eq204441 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq204398 eq31
    | exact resolve eq31 eq204398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq204826 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq204398 eq195195
    | (have r₁ := eq195195
       have r₂ := eq204398
       grind)
    | exact resolve eq195195 eq204398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195195
  have eq204840 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq204398 eq202574
    | exact resolve eq202574 eq204398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202574 eq204398
  have eq204841 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq204840
  have eq204855 : (σ x) ≠ (σ x) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq204826
  have eq204856 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq204855
  have eq205246 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq204441
    | exact resolve eq204441 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204441
  have eq205268 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq204856 eq27
    | exact resolve eq27 eq204856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204856
  have eq205466 : (M.op x y) = (M.op x (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq205246
       grind)
    | exact superpose eq205246 eq18
    | exact resolve eq18 eq205246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205471 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq205246
  have eq206112 : ∀ X0 : G, x = (M.op (M.op x y) (M.op X0 X0)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq205466 eq174
    | exact resolve eq174 eq205466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq205466
  have eq281568 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq204841
       have i₂ := eq202834 sF2
       grind)
    | exact superpose eq202834 eq204841
    | exact resolve eq204841 eq202834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204841
  have eq281582 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq203326
       have i₂ := eq202834 sF3
       grind)
    | exact superpose eq202834 eq203326
    | exact resolve eq203326 eq202834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202834 eq203326
  have eq281599 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (k x y) := by grind
  clear eq281582
  have eq281611 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ y = (k x y) := by grind
  clear eq281568
  have eq282058 : (σ x) = (k (σ y) (σ y)) ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | (have r₁ := eq281599
       have r₂ := eq1038
       grind)
    | exact resolve eq281599 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281599
  have eq282067 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | (have r₁ := eq281611
       have r₂ := eq1038
       grind)
    | exact resolve eq281611 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281611
  have eq292522 : (τ (σ x)) = (k y y) ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq282058 eq115
    | exact resolve eq115 eq282058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq282058
  have eq292658 : y = (k x y) ∨ y = (M.op y y) ∨ x = (k y y) := by
    first
    | exact superpose eq29 eq292522
    | exact resolve eq292522 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq292522
  have eq296489 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq1759 x y
       have i₂ := eq292658
       grind)
    | exact superpose eq292658 eq1759
    | (have j0 := eq1759 x y
       grind)
    | exact resolve eq1759 eq292658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1759 eq292658
  have eq296505 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (k y y) := by grind
  clear eq296489
  have eq296524 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq296505
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq296505
    | exact resolve eq296505 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296505
  have eq296552 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq296524
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq296524
    | exact resolve eq296524 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296524
  have eq296565 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) ∨ x = (k y y) := by
    first
    | exact superpose eq26 eq296552
    | exact resolve eq296552 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296552
  have eq296570 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq296565
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq296565
    | exact resolve eq296565 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296565
  have eq296572 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1251 eq296570
    | exact resolve eq296570 eq1251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1251 eq296570
  have eq296574 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1897 eq296572
    | exact resolve eq296572 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897 eq296572
  have eq296576 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq143880 eq296574
    | exact resolve eq296574 eq143880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143880 eq296574
  have eq296578 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq1128 (σ y)
       grind)
    | (have r₁ := eq296576
       have r₂ := eq1128 (M.op x y)
       grind)
    | exact resolve eq296576 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296576
  have eq296633 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 X0) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq296578 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq296578
       grind)
    | (have r₁ := eq13 X0 (M.op x y)
       have r₂ := eq296578
       grind)
    | exact resolve eq13 eq296578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq296771 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq296633 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296633
  have eq308607 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | exact superpose eq282067 eq1180
    | exact resolve eq1180 eq282067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1180 eq282067
  have eq308689 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (k x y) := by grind
  clear eq308607
  have eq308705 : y = (M.op x y) ∨ y = (M.op y y) ∨ y = (k x y) := by
    first
    | (have r₁ := eq308689
       have r₂ := eq205268
       grind)
    | exact resolve eq308689 eq205268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205268 eq308689
  have eq308735 : y = (k x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq308705
       have r₂ := eq1038
       grind)
    | exact resolve eq308705 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038 eq308705
  have eq310810 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq296578
       have i₂ := eq296771 sF3
       grind)
    | exact superpose eq296771 eq296578
    | exact resolve eq296578 eq296771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296578 eq296771
  have eq310824 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq310810
  have eq311344 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq310824 eq152
    | exact resolve eq152 eq310824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq310824
  have eq311505 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq31 eq311344
    | exact resolve eq311344 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq311344
  have eq311508 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq197711 eq311505
    | exact resolve eq311505 eq197711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197711 eq311505
  have eq311511 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1128 (M.op x y)
       grind)
    | (have r₁ := eq311508
       have r₂ := eq1128 (M.op x y)
       grind)
    | exact resolve eq311508 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311508
  have eq311666 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq311511 eq206112
    | exact resolve eq206112 eq311511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206112
  have eq311776 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36500 eq311666
    | exact resolve eq311666 eq36500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36500 eq311666
  have eq311805 : x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq311511 eq311776
    | exact resolve eq311776 eq311511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311511 eq311776
  have eq311806 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq311805
  have eq311820 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq311806 eq27
    | exact resolve eq27 eq311806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311806
  have eq311858 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq110592 eq311820
    | (have r₁ := eq311820
       have r₂ := eq110592
       grind)
    | exact resolve eq311820 eq110592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110592 eq311820
  have eq311859 : (σ y) ≠ (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq311858
  have eq311860 : x = (M.op x y) ∨ x = y := by grind
  clear eq311859
  have eq311862 : x = y := by
    first
    | (have r₁ := eq311860
       have r₂ := eq205471
       grind)
    | exact resolve eq311860 eq205471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205471 eq311860
  have eq311866 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq311862
       grind)
    | exact superpose eq311862 eq18
    | exact resolve eq18 eq311862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq311867 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq311862
       grind)
    | exact superpose eq311862 eq24
    | exact resolve eq24 eq311862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq312216 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq308735
       have i₂ := eq311862
       grind)
    | exact superpose eq311862 eq308735
    | exact resolve eq308735 eq311862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308735
  have eq312239 : x = (M.op x x) := by
    first
    | (have j1 := eq1128 x
       grind)
    | (have r₁ := eq312216
       have r₂ := eq1128 x
       grind)
    | exact resolve eq312216 eq1128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1128 eq312216
  have eq312262 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq311867
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq311867
    | exact resolve eq311867 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311867
  have eq312263 : x = (M.op x y) := by
    first
    | (have i₁ := eq312239
       have i₂ := eq311866
       grind)
    | exact superpose eq311866 eq312239
    | exact resolve eq312239 eq311866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312239
  have eq312267 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq312262 eq26
    | exact resolve eq26 eq312262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq312262
  have eq312783 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq312263
       grind)
    | exact superpose eq312263 eq18
    | exact resolve eq18 eq312263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq312784 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq312263
       grind)
    | exact superpose eq312263 eq22
    | exact resolve eq22 eq312263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq313123 : (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq312783
       have i₂ := eq311862
       grind)
    | exact superpose eq311862 eq312783
    | exact resolve eq312783 eq311862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311862 eq312783
  have eq313127 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq313123
       have i₂ := eq312263
       grind)
    | exact superpose eq312263 eq313123
    | exact resolve eq313123 eq312263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313123
  have eq313902 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq312784 eq20
    | exact resolve eq20 eq312784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312784
  have eq314671 : ∀ X0 : G, x ≠ (M.op x y) ∨ (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq311866
       grind)
    | exact superpose eq311866 eq13
    | (have j0 := eq13 X0 x
       grind)
    | exact resolve eq13 eq311866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq314678 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq180 x
       have i₂ := eq311866
       grind)
    | exact superpose eq311866 eq180
    | exact resolve eq180 eq311866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq314681 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq546 X0 X1 x
       have i₂ := eq311866
       grind)
    | exact superpose eq311866 eq546
    | exact resolve eq546 eq311866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq546 eq311866
  have eq314815 : ∀ X0 : G, (M.op X0 X0) = (k X0 x) := by
    intro X0
    first
    | (have j0 := eq314671 X0
       grind)
    | (have r₁ := eq314671 X0
       have r₂ := eq312263
       grind)
    | exact resolve eq314671 eq312263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314671
  have eq314821 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq314815 X0
       have i₂ := eq312263
       grind)
    | exact superpose eq312263 eq314815
    | exact resolve eq314815 eq312263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312263 eq314815
  have eq317462 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq313127
       have i₂ := eq314821 sF0
       grind)
    | exact superpose eq314821 eq313127
    | exact resolve eq313127 eq314821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313127 eq314821
  have eq317820 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq317462 eq37
    | exact resolve eq37 eq317462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq317462
  have eq317937 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq317820
    | exact resolve eq317820 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq317820
  have eq317944 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq313902 eq317937
    | exact resolve eq317937 eq313902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317937
  have eq318113 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq317944 eq1134
    | (have j0 := eq1134 (σ x)
       grind)
    | exact resolve eq1134 eq317944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq318150 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (k (σ x) (σ x)) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq317944 eq2984
    | (have j0 := eq2984 (σ x) (σ x) x
       grind)
    | exact resolve eq2984 eq317944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2984
  have eq318161 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (k (σ x) (σ x)) (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq318150 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318150
  have eq318186 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (k (σ x) (σ x)) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq312267 eq318161
    | (have j0 := eq318161 X0
       grind)
    | exact resolve eq318161 eq312267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318161
  have eq318206 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq312267 eq318113
    | exact resolve eq318113 eq312267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318113
  have eq318216 : (σ x) = (M.op (k (σ x) (σ x)) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq318186 x
       have i₂ := eq314681 (k sF2 sF2) x
       grind)
    | exact superpose eq314681 eq318186
    | exact resolve eq318186 eq314681
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314681 eq318186
  have eq318231 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq314678 eq318206
    | exact resolve eq318206 eq314678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314678 eq318206
  have eq318240 : (σ x) = (M.op (σ x) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq317944 eq318216
    | exact resolve eq318216 eq317944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317944 eq318216
  have eq318252 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq312267 eq318231
    | exact resolve eq318231 eq312267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312267 eq318231
  have eq318262 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq318240 eq318252
    | exact resolve eq318252 eq318240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq318240 eq318252
  have eq318263 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq318262
  have eq318280 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq318263 eq27
    | exact resolve eq27 eq318263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq318263
  have eq318394 : False := by grind
  exact eq318394

/-- `Equation1872`: `x = (x ◇ (y ◇ z)) ◇ (y ◇ y)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_pxy_x_pyx_Equation1872 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1872 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1872.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X1 X1)) = X0 := by
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
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ (k X1 (k X0 x))) = (k (σ X1) (k (σ X0) (σ x))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (k X0 x)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq10
    | exact resolve eq10 eq39
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
  have eq133 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq50
    | (have j0 := eq50 (M.op x y)
       grind)
    | exact resolve eq50 eq20
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
  clear eq59
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
  have eq175 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X1 X2)) X1 X1
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : y ≠ (M.op x y) ∨ (k y x) = (M.op y x) := by
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
  have eq179 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 X1 X2 : G, (M.op X1 X1) ≠ X0 ∨ (k (M.op X1 X1) (M.op X0 (M.op X1 X2))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X1 X1) (M.op X0 (M.op X1 X2))
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 (M.op X1 X1) (M.op X0 (M.op X1 X2))
       grind)
    | (have r₁ := eq13 (M.op X1 X1) (M.op (M.op X1 X1) (M.op X1 X2))
       have r₂ := eq16 (M.op X1 X1) X1 X2
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq631 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq177 X0 X1 X2
       have i₂ := eq177 X0 X1 X3
       grind)
    | (have i₁ := eq177 X0 X2 X2
       have i₂ := eq177 X0 X2 X2
       grind)
    | exact superpose eq177 eq177
    | exact resolve eq177 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq657 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X1 X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq177 (M.op X0 (M.op X1 X2)) X1 X3
       grind)
    | (have i₁ := eq16 X0 X2 X2
       have i₂ := eq177 (M.op X0 (M.op X2 X2)) X2 X2
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq704 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op X1 (M.op (M.op X0 (M.op X2 X3)) X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq631 X1 (M.op X0 (M.op X2 X3)) X4 (M.op X2 X2)
       have i₂ := eq16 X0 X2 X3
       grind)
    | exact superpose eq16 eq631
    | exact resolve eq631 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq844 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X0 (M.op X0 X2)) X3)) X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X1 (M.op X0 (M.op X0 X2)) X3
       have i₂ := eq657 X0 X0 X2 (M.op X0 X2)
       grind)
    | exact superpose eq657 eq16
    | exact resolve eq16 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq850 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq844 X0 X1 x x
       have i₂ := eq704 X0 X1 X0 x x
       grind)
    | exact superpose eq704 eq844
    | exact resolve eq844 eq704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704 eq844
  have eq887 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq850 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq850
    | (have j0 := eq850 y x
       grind)
    | exact resolve eq850 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq888 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq850
    | (have j0 := eq850 (σ y) (σ x)
       grind)
    | exact resolve eq850 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq901 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op X0 X2) X3)) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq657 X1 (M.op X0 X2) X2 X3
       have i₂ := eq850 X2 X0
       grind)
    | exact superpose eq850 eq657
    | exact resolve eq657 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq902 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X0 X2) X3)) X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq657 X1 (M.op X0 X2) X3 X2
       have i₂ := eq850 X2 X0
       grind)
    | exact superpose eq850 eq657
    | exact resolve eq657 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq923 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X0 (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq887 eq631
    | exact resolve eq631 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq924 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op (M.op x y) X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq887 eq657
    | exact resolve eq657 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq944 : y ≠ (M.op x y) ∨ x = (M.op y x) ∨ x = (k x y) := by
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
  have eq946 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq968 : (M.op x y) = (k y x) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
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
  have eq970 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq972 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 X0)) = X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
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
  have eq974 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1015 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (k (σ x) (σ x))) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq11 sF2 sF2
       grind)
    | exact superpose eq11 eq175
    | (have j1 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq175 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1018 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1019 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1020 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1018 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1018
  have eq1021 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (k (σ x) (σ x))) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq1015 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1015
  have eq1026 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 X0)) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq972 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq1048 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq974 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq974 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq974 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq974 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq1065 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq888 eq631
    | exact resolve eq631 eq888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq1328 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1020 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1020
    | (have j0 := eq1020 (σ X0)
       grind)
    | exact resolve eq1020 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1866 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq968
       grind)
    | exact superpose eq968 eq39
    | exact resolve eq39 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1867 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1866
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1866
    | exact resolve eq1866 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1866
  have eq1869 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1867
    | exact resolve eq1867 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1867
  have eq2273 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1869 eq970
    | exact resolve eq970 eq1869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2280 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2273
       have r₂ := eq27
       grind)
    | exact resolve eq2273 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2273
  have eq2286 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2280 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq2280
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq2280
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2280
       grind)
    | exact resolve eq12 eq2280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2280
  have eq2301 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq2286
  have eq2309 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2301
    | exact resolve eq2301 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2301
  have eq2310 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq2309
  have eq2360 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2310 eq141
    | exact resolve eq141 eq2310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2310
  have eq2365 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq2360
    | exact resolve eq2360 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2360
  have eq2368 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq968 eq2365
    | exact resolve eq2365 eq968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2365
  have eq2369 : x = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2368
  have eq2373 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2369
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq2369
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq2369 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2375 : x ≠ x ∨ y = (M.op x y) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq2369
       grind)
    | exact superpose eq2369 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq2369
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq2369
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq2369
       grind)
    | exact resolve eq12 eq2369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2376 : x ≠ x ∨ (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2369
       grind)
    | exact superpose eq2369 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2369
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2369
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2369
       grind)
    | exact resolve eq13 eq2369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2389 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2376
  have eq2390 : y = (M.op x y) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2375
  have eq2397 : (M.op x y) = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2389
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2389
    | exact resolve eq2389 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2389
  have eq2398 : y = (M.op x y) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
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
  have eq2399 : y = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2398
  have eq2401 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq2373
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq2373
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq2373
       have r₂ := eq12 y x
       grind)
    | exact resolve eq2373 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2373
  have eq2402 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq2401
       have r₂ := eq944
       grind)
    | exact resolve eq2401 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2401
  have eq2403 : x = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2369 eq2402
    | exact resolve eq2402 eq2369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2369 eq2402
  have eq2548 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq2397
       grind)
    | exact superpose eq2397 eq40
    | exact resolve eq40 eq2397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2397
  have eq2550 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2548
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2548
    | exact resolve eq2548 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2548
  have eq2552 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq2550
    | exact resolve eq2550 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2550
  have eq2557 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq2399
       grind)
    | exact superpose eq2399 eq39
    | exact resolve eq39 eq2399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2399
  have eq2562 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2557
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2557
    | exact resolve eq2557 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2557
  have eq2594 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2562 eq970
    | exact resolve eq970 eq2562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2562
  have eq2600 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2594
  have eq2623 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2600
       have i₂ := eq11 sF2 sF3
       grind)
    | exact superpose eq11 eq2600
    | (have j1 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq2600 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2626 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2600 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2600
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2600
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2600
       grind)
    | exact resolve eq13 eq2600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2600
  have eq2640 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq2626
  have eq2648 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq2640
    | exact resolve eq2640 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2640
  have eq2650 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have j1 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq2623
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq2623
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq2623
       have r₂ := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq2623 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2623
  have eq2651 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2552 eq2648
    | exact resolve eq2648 eq2552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2552 eq2648
  have eq2652 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq2650
       have r₂ := eq946
       grind)
    | exact resolve eq2650 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq946 eq2650
  have eq2653 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq2651
       have r₂ := eq27
       grind)
    | exact resolve eq2651 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2651
  have eq2654 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2653 eq27
    | exact resolve eq27 eq2653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2656 : (σ y) ≠ (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2653 eq179
    | (have r₁ := eq179
       have r₂ := eq2653
       grind)
    | exact resolve eq179 eq2653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq2664 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (σ y) X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2653 eq1065
    | exact resolve eq1065 eq2653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq2668 : (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq2656
  have eq2749 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ y) X1)) (k (σ y) (σ x))) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq2668 eq657
    | exact resolve eq657 eq2668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq657
  have eq2762 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (k (σ y) (σ x))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2664 eq2749
    | exact resolve eq2749 eq2664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2664 eq2749
  have eq3093 : (σ y) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2668 eq2762
    | exact resolve eq2762 eq2668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2762
  have eq3124 : (σ y) = (M.op (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ y = (M.op x y) := by grind
  clear eq3093
  have eq3377 : (σ y) = (k (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3124 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq3124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3379 : (σ y) ≠ (k (σ y) (σ x)) ∨ (σ y) = (k (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3124 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq3124
       grind)
    | exact resolve eq13 eq3124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3124
  have eq3393 : (σ y) = (k (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq3377
  have eq3405 : (σ y) = (k (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3393
       have r₂ := eq3379
       grind)
    | exact resolve eq3393 eq3379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3379 eq3393
  have eq3461 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1869 eq3405
    | exact resolve eq3405 eq1869
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3405
  have eq3467 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq3461
  have eq3864 : x ≠ x ∨ (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2403 eq1019
    | (have j0 := eq1019 (M.op x y) x
       grind)
    | (have r₁ := eq1019 (M.op x y) x
       have r₂ := eq2403
       grind)
    | exact resolve eq1019 eq2403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2403
  have eq3865 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by grind
  clear eq3864
  have eq3867 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq2653 eq3865
    | exact resolve eq3865 eq2653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3865
  have eq3868 : (M.op x y) = (M.op x (M.op x y)) ∨ x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3867
  have eq3904 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X1))) = (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq180 (M.op X0 X0) X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq3906 : ∀ X0 X1 : G, (k (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3904 X0 X1
       have i₂ := eq901 X0 X0 X0 (M.op X0 X1)
       grind)
    | exact superpose eq901 eq3904
    | exact resolve eq3904 eq901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq901 eq3904
  have eq3923 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3868 eq13
    | (have j0 := eq13 (M.op x y) x
       grind)
    | (have r₁ := eq13 (M.op x y) x
       have r₂ := eq3868
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq3868
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq3868
       grind)
    | exact resolve eq13 eq3868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3868
  have eq3939 : (k (M.op x y) x) = (M.op (M.op x y) x) ∨ x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq3923
  have eq4155 : (τ (σ x)) = (k (τ (σ x)) y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq2652 eq152
    | exact resolve eq152 eq2652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq2652
  have eq4167 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq29 eq4155
    | exact resolve eq4155 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4155
  have eq4196 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq4167 eq2668
    | exact resolve eq2668 eq4167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2668
  have eq4205 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq4167 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq4167
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq4167
       grind)
    | exact resolve eq13 eq4167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4167
  have eq4221 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x y) := by grind
  clear eq4205
  have eq4229 : (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (k x y) := by grind
  clear eq4196
  have eq4239 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq26 eq4221
    | exact resolve eq4221 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4221
  have eq4246 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq2653 eq4239
    | exact resolve eq4239 eq2653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4239
  have eq4328 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq4229 eq1869
    | exact resolve eq1869 eq4229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1869
  have eq4338 : (τ (σ x)) = (k y (τ (σ x))) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq4229 eq107
    | exact resolve eq107 eq4229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq4229
  have eq4353 : (σ (M.op x y)) = (σ x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (k x y) := by grind
  clear eq4328
  have eq4358 : x = (k y x) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq29 eq4338
    | exact resolve eq4338 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4338
  have eq4359 : x = (k x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq4353
       have r₂ := eq944
       grind)
    | exact resolve eq4353 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4353
  have eq4448 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq968
       have i₂ := eq4358
       grind)
    | exact superpose eq4358 eq968
    | exact resolve eq968 eq4358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq968 eq4358
  have eq4454 : x = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (k x y) := by grind
  clear eq4448
  have eq4462 : x = (k x y) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4454
       have r₂ := eq944
       grind)
    | exact resolve eq4454 eq944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4454
  have eq4470 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq4359
       grind)
    | exact superpose eq4359 eq40
    | exact resolve eq40 eq4359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4472 : x ≠ x ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1019 y x
       have i₂ := eq4359
       grind)
    | exact superpose eq4359 eq1019
    | (have j0 := eq1019 y x
       grind)
    | (have r₁ := eq1019 y x
       have r₂ := eq4359
       grind)
    | exact resolve eq1019 eq4359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4359
  have eq4473 : x ≠ x ∨ y = (M.op x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4472
  have eq4474 : y = (M.op x y) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4473
  have eq4476 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4474
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4474
    | exact resolve eq4474 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4474
  have eq4478 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4470
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4470
    | exact resolve eq4470 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4470
  have eq4485 : x ≠ x ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq4476
       grind)
    | exact superpose eq4476 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq4476
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq4476
       grind)
    | exact resolve eq13 eq4476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4476
  have eq4501 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq4485
  have eq4511 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq4501
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4501
    | exact resolve eq4501 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4501
  have eq5052 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq4511
       grind)
    | exact superpose eq4511 eq40
    | exact resolve eq40 eq4511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5057 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq5052
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5052
    | exact resolve eq5052 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5052
  have eq5059 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq5057
    | exact resolve eq5057 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5057
  have eq5095 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (k x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq5059 eq4246
    | exact resolve eq4246 eq5059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4246 eq5059
  have eq5105 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq5095
  have eq5112 : y = (M.op x y) ∨ x = (k x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq5105
       have r₂ := eq2654
       grind)
    | exact resolve eq5105 eq2654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2654 eq5105
  have eq5116 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4511 eq5112
    | exact resolve eq5112 eq4511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4511 eq5112
  have eq5118 : (M.op x y) = (τ (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5116 eq28
    | exact resolve eq28 eq5116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq5116
  have eq5144 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq5118
    | exact resolve eq5118 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5118
  have eq5145 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5144
  have eq5149 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq5145
       grind)
    | exact superpose eq5145 eq24
    | exact resolve eq24 eq5145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5152 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq178
       have i₂ := eq5145
       grind)
    | exact superpose eq5145 eq178
    | (have r₁ := eq178
       have r₂ := eq5145
       grind)
    | exact resolve eq178 eq5145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5153 : x = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq887
       have i₂ := eq5145
       grind)
    | exact superpose eq5145 eq887
    | exact resolve eq887 eq5145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5158 : (k (M.op x y) x) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq5152
  have eq5161 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq5149
    | exact resolve eq5149 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5149
  have eq5243 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5153 eq11
    | exact resolve eq11 eq5153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5262 : (M.op x y) = (k x (M.op x x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5153 eq3906
    | exact resolve eq3906 eq5153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5153
  have eq5265 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq5243
  have eq5310 : ∀ X0 : G, (M.op (M.op X0 x) (k (M.op x y) x)) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5158 eq924
    | exact resolve eq924 eq5158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq5326 : (M.op x y) = (M.op (k (M.op x y) x) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5158 eq850
    | exact resolve eq850 eq5158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5360 : (σ (M.op x y)) = (k (σ x) (σ (M.op x x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35 (M.op x x)
       have i₂ := eq5262
       grind)
    | exact superpose eq5262 eq35
    | exact resolve eq35 eq5262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5262
  have eq5364 : (σ (M.op x y)) = (k (σ x) (σ (M.op x x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq5360
    | exact resolve eq5360 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5360
  have eq5365 : (σ y) = (k (σ x) (σ (M.op x x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5161 eq5364
    | exact resolve eq5364 eq5161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5364
  have eq6000 : (M.op x y) = (M.op (k (M.op x y) x) (k (M.op x y) x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5158 eq5310
    | exact resolve eq5310 eq5158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5310
  have eq6025 : (M.op x y) = (M.op (k (M.op x y) x) (k (M.op x y) x)) ∨ x = (M.op x y) := by grind
  clear eq6000
  have eq6112 : (M.op x y) = (k (k (M.op x y) x) (k (M.op x y) x)) ∨ (M.op x y) = (k (M.op x y) x) ∨ (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6025 eq11
    | exact resolve eq11 eq6025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6114 : (M.op x y) ≠ (k (M.op x y) x) ∨ (M.op x y) = (k (k (M.op x y) x) (k (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6025 eq13
    | exact resolve eq13 eq6025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6025
  have eq6132 : (M.op x y) = (k (k (M.op x y) x) (k (M.op x y) x)) ∨ (M.op x y) = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq6112
  have eq6144 : (M.op x y) = (k (k (M.op x y) x) (k (M.op x y) x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq6132
       have r₂ := eq6114
       grind)
    | exact resolve eq6132 eq6114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6114 eq6132
  have eq6446 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq4462
       grind)
    | exact superpose eq4462 eq40
    | exact resolve eq40 eq4462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4462
  have eq6460 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6446
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6446
    | exact resolve eq6446 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6446
  have eq6464 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5145 eq6460
    | exact resolve eq6460 eq5145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6460
  have eq6479 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq4478 eq1048
    | (have j0 := eq1048 (σ x) (σ y)
       grind)
    | (have r₁ := eq1048 (σ x) (σ y)
       have r₂ := eq4478
       grind)
    | exact resolve eq1048 eq4478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4478
  have eq6482 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq6479
  have eq6491 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq6482
    | exact resolve eq6482 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6482
  have eq6496 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq26 eq6491
    | exact resolve eq6491 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6491
  have eq6498 : x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq2653 eq6496
    | exact resolve eq6496 eq2653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2653 eq6496
  have eq6505 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq3467 eq133
    | exact resolve eq133 eq3467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq3467
  have eq6518 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq31 eq6505
    | exact resolve eq6505 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6505
  have eq6522 : (M.op x y) = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5145 eq6518
    | exact resolve eq6518 eq5145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6518
  have eq6768 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6464 eq1048
    | (have j0 := eq1048 (σ x) (σ y)
       grind)
    | (have r₁ := eq1048 (σ x) (σ y)
       have r₂ := eq6464
       grind)
    | exact resolve eq1048 eq6464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6464
  have eq6771 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq6768
  have eq6775 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq6771
    | exact resolve eq6771 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6771
  have eq6780 : x = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq6775
    | exact resolve eq6775 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6775
  have eq6813 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x y) X1)) y) = X0 ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq6522 eq902
    | exact resolve eq902 eq6522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq902
  have eq6823 : ∀ X0 : G, (M.op (M.op X0 x) y) = X0 ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq923 eq6813
    | exact resolve eq6813 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6813
  have eq6838 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) y) = X0 ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq5145 eq6823
    | exact resolve eq6823 eq5145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6823
  have eq9448 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq6498 eq850
    | exact resolve eq850 eq6498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9750 : x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6780 eq5158
    | exact resolve eq5158 eq6780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5158
  have eq9768 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6780 eq850
    | exact resolve eq850 eq6780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6780
  have eq9780 : x = (k (M.op x y) x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9750
  have eq9809 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq9448
       grind)
    | exact superpose eq9448 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq9448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9811 : x ≠ (M.op x y) ∨ (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq9448
       grind)
    | exact superpose eq9448 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq9448
       grind)
    | exact resolve eq13 eq9448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9448
  have eq9829 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq9809
  have eq9842 : (M.op x y) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq9829
       have r₂ := eq9811
       grind)
    | exact resolve eq9829 eq9811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9811 eq9829
  have eq9880 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5365
       have i₂ := eq9768
       grind)
    | exact superpose eq9768 eq5365
    | exact resolve eq5365 eq9768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5365 eq9768
  have eq9915 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq9880
  have eq9933 : (σ y) = (k (σ x) (σ (M.op x y))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq9915
    | exact resolve eq9915 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9915
  have eq9936 : (σ y) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5161 eq9933
    | exact resolve eq9933 eq5161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9933
  have eq10694 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq9780 eq37
    | exact resolve eq37 eq9780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9780
  have eq10717 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10694
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10694
    | exact resolve eq10694 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10694
  have eq10722 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5161 eq10717
    | exact resolve eq10717 eq5161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10717
  have eq10731 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10722 eq970
    | exact resolve eq970 eq10722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970 eq10722
  have eq10763 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10731
  have eq10984 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq10763 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq10763
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq10763
       grind)
    | exact resolve eq13 eq10763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10763
  have eq11002 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq10984
  have eq11013 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq11002
    | exact resolve eq11002 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11002
  have eq11018 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9936 eq11013
    | exact resolve eq11013 eq9936
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9936 eq11013
  have eq11019 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11018
  have eq11022 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11019 eq27
    | exact resolve eq27 eq11019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11019
  have eq11040 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11022
       have r₂ := eq5161
       grind)
    | exact resolve eq11022 eq5161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11022
  have eq11045 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11040 eq27
    | exact resolve eq27 eq11040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11075 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5161 eq11045
    | exact resolve eq11045 eq5161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5161 eq11045
  have eq11079 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq11075
  have eq11883 : (M.op x y) = (M.op (k (M.op x y) x) x) ∨ x = (M.op (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3939 eq850
    | exact resolve eq850 eq3939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3939
  have eq11902 : (M.op x y) = (M.op (k (M.op x y) x) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5326 eq11883
    | exact resolve eq11883 eq5326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5326 eq11883
  have eq12437 : (k (M.op x y) x) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11902 eq850
    | exact resolve eq850 eq11902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11902
  have eq12484 : x = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12437 eq6498
    | exact resolve eq6498 eq12437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6498 eq12437
  have eq12515 : x = (k (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq12484
  have eq12536 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq11040 eq12515
    | exact resolve eq12515 eq11040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12515
  have eq12542 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq1020 (M.op x y)
       grind)
    | (have r₁ := eq12536
       have r₂ := eq1020 (M.op x y)
       grind)
    | exact resolve eq12536 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020 eq12536
  have eq12566 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12542 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq12542
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq12542
       grind)
    | exact resolve eq13 eq12542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12542
  have eq12583 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq12566
  have eq16099 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq6522 eq6838
    | exact resolve eq6838 eq6522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6522 eq6838
  have eq16135 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by grind
  clear eq16099
  have eq16142 : x = y ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq887 eq16135
    | exact resolve eq16135 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16135
  have eq16146 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq5145 eq16142
    | exact resolve eq16142 eq5145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16142
  have eq16147 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq16146
  have eq16161 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op x y) X1)) y) = X0 ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq16147 eq1026
    | (have j0 := eq1026 (M.op x y) X1 x
       grind)
    | exact resolve eq1026 eq16147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq16168 : ∀ X0 : G, (M.op (M.op X0 x) y) = X0 ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq923 eq16161
    | exact resolve eq16161 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923 eq16161
  have eq16171 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) y) = X0 ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5145 eq16168
    | exact resolve eq16168 eq5145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16168
  have eq18504 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq16171 eq850
    | exact resolve eq850 eq16171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16171
  have eq19475 : x = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq887
       have i₂ := eq18504 sF0
       grind)
    | exact superpose eq18504 eq887
    | exact resolve eq887 eq18504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18504
  have eq19545 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5145 eq19475
    | exact resolve eq19475 eq5145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5145 eq19475
  have eq19546 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq19545
  have eq19588 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19546 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq19546
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19546
       grind)
    | exact resolve eq13 eq19546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19546
  have eq19605 : (M.op x y) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by grind
  clear eq19588
  have eq19665 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq19605 eq16147
    | exact resolve eq16147 eq19605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16147 eq19605
  have eq19677 : y = (M.op x y) := by grind
  clear eq19665
  have eq19687 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq19677
       grind)
    | exact superpose eq19677 eq18
    | exact resolve eq18 eq19677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq19688 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq19677
       grind)
    | exact superpose eq19677 eq24
    | exact resolve eq24 eq19677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq19689 : ∀ X0 : G, (k (σ y) (σ X0)) = (σ (k (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq19677
       grind)
    | exact superpose eq19677 eq36
    | exact resolve eq36 eq19677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq19690 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq19677
       grind)
    | exact superpose eq19677 eq40
    | exact resolve eq40 eq19677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq19691 : (M.op x y) ≠ (M.op x y) ∨ (k (M.op x y) x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq178
       have i₂ := eq19677
       grind)
    | exact superpose eq19677 eq178
    | (have r₁ := eq178
       have r₂ := eq19677
       grind)
    | exact resolve eq178 eq19677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq19692 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq887
       have i₂ := eq19677
       grind)
    | exact superpose eq19677 eq887
    | exact resolve eq887 eq19677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq19694 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op (M.op x y) x) ∨ x = (k x (M.op x y)) := by
    first
    | (have i₁ := eq944
       have i₂ := eq19677
       grind)
    | exact superpose eq19677 eq944
    | (have r₁ := eq944
       have r₂ := eq19677
       grind)
    | exact resolve eq944 eq19677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq944
  have eq19698 : x = (k x (M.op x y)) ∨ x = (M.op (M.op x y) x) := by grind
  clear eq19694
  have eq19699 : (k (M.op x y) x) = (M.op (M.op x y) x) := by grind
  clear eq19691
  have eq19702 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq19688 eq20
    | exact resolve eq20 eq19688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19721 : ∀ X0 : G, (σ (k X0 (k (M.op x y) x))) = (k (σ X0) (k (σ y) (σ x))) := by
    intro X0
    first
    | exact superpose eq19688 eq57
    | exact resolve eq57 eq19688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq19737 : ∀ X0 : G, (τ (k (σ y) X0)) = (k (M.op x y) (τ X0)) := by
    intro X0
    first
    | exact superpose eq19688 eq437
    | exact resolve eq437 eq19688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437
  have eq19928 : x ≠ (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq19692 eq13
    | exact resolve eq13 eq19692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19945 : (M.op x y) = (k x (M.op x x)) := by
    first
    | exact superpose eq19692 eq3906
    | exact resolve eq3906 eq19692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19953 : x = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq19928
       have r₂ := eq5265
       grind)
    | exact resolve eq19928 eq5265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5265 eq19928
  have eq19975 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq19953 eq37
    | exact resolve eq37 eq19953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq19953
  have eq19986 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq19975
    | exact resolve eq19975 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19975
  have eq19990 : (σ x) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq19702 eq19986
    | exact resolve eq19986 eq19702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19986
  have eq19992 : (σ x) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq19990
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19990
    | exact resolve eq19990 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19990
  have eq20030 : x ≠ (k (M.op x y) x) ∨ (k x (M.op x y)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq19699 eq13
    | (have j0 := eq13 x (M.op x y)
       grind)
    | exact resolve eq13 eq19699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20041 : (M.op x y) = (M.op (k (M.op x y) x) x) := by
    first
    | exact superpose eq19699 eq850
    | exact resolve eq850 eq19699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20062 : x ≠ (k (M.op x y) x) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq19687 eq20030
    | exact resolve eq20030 eq19687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19687 eq20030
  have eq20088 : (σ (M.op x y)) = (k (σ x) (σ (M.op x x))) := by
    first
    | (have i₁ := eq35 (M.op x x)
       have i₂ := eq19945
       grind)
    | exact superpose eq19945 eq35
    | exact resolve eq35 eq19945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19945
  have eq20093 : (σ (M.op x y)) = (k (σ x) (σ (M.op x x))) := by
    first
    | exact superpose eq20 eq20088
    | exact resolve eq20088 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20088
  have eq20095 : (σ y) = (k (σ x) (σ (M.op x x))) := by
    first
    | exact superpose eq19702 eq20093
    | exact resolve eq20093 eq19702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20093
  have eq20162 : (σ x) ≠ (σ y) ∨ (σ (M.op x x)) = (M.op (σ x) (σ (M.op x x))) ∨ (σ x) = (M.op (σ (M.op x x)) (σ x)) := by
    first
    | exact superpose eq20095 eq1019
    | (have j0 := eq1019 (σ (M.op x x)) (σ x)
       grind)
    | exact resolve eq1019 eq20095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20095
  have eq20164 : (σ x) ≠ (σ y) ∨ (σ (M.op (M.op x y) (M.op x y))) = (M.op (σ x) (σ (M.op (M.op x y) (M.op x y)))) ∨ (σ x) = (M.op (σ (M.op x x)) (σ x)) := by
    first
    | exact superpose eq11079 eq20162
    | exact resolve eq20162 eq11079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20162
  have eq20173 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ (M.op x x)) (σ x)) := by
    first
    | exact superpose eq19692 eq20164
    | exact resolve eq20164 eq19692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20164
  have eq20179 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ (M.op x x)) (σ x)) := by
    first
    | (have i₁ := eq20173
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20173
    | exact resolve eq20173 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20173
  have eq20182 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ x)) := by
    first
    | exact superpose eq11079 eq20179
    | exact resolve eq20179 eq11079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20179
  have eq20184 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ y) := by
    first
    | exact superpose eq19692 eq20182
    | exact resolve eq20182 eq19692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19692 eq20182
  have eq20186 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq20184
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20184
    | exact resolve eq20184 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20184
  have eq20187 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq20186
  have eq20199 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12583 eq19689
    | exact resolve eq19689 eq12583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12583 eq19689
  have eq20296 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq20199
    | exact resolve eq20199 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20199
  have eq20319 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19702 eq20296
    | exact resolve eq20296 eq19702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20296
  have eq20329 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19992 eq20319
    | exact resolve eq20319 eq19992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20319
  have eq20334 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19702 eq20329
    | exact resolve eq20329 eq19702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20329
  have eq20335 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20334
  have eq20789 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20335 eq27
    | exact resolve eq27 eq20335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20812 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq20789
       have r₂ := eq19702
       grind)
    | exact resolve eq20789 eq19702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20789
  have eq20860 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq19698 eq19690
    | exact resolve eq19690 eq19698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19690 eq19698
  have eq20870 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq20860
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20860
    | exact resolve eq20860 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20860
  have eq20873 : (σ x) = (k (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq19699 eq20870
    | exact resolve eq20870 eq19699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19699 eq20870
  have eq21058 : (σ x) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1328 x
       have i₂ := eq9842
       grind)
    | exact superpose eq9842 eq1328
    | (have j0 := eq1328 x
       grind)
    | exact resolve eq1328 eq9842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1328 eq9842
  have eq21130 : (σ x) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq20 eq21058
    | exact resolve eq21058 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21058
  have eq21153 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq19702 eq21130
    | exact resolve eq21130 eq19702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21130
  have eq21165 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq21153
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21153
    | exact resolve eq21153 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21153
  have eq21174 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have r₁ := eq21165
       have r₂ := eq20335
       grind)
    | exact resolve eq21165 eq20335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20335 eq21165
  have eq21182 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq21174
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq21174
    | exact resolve eq21174 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21174
  have eq21185 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19702 eq21182
    | exact resolve eq21182 eq19702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21182
  have eq21187 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq21185
       have r₂ := eq20187
       grind)
    | exact resolve eq21185 eq20187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21185
  have eq21188 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20812 eq21187
    | exact resolve eq21187 eq20812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21187
  have eq21189 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21188
  have eq21230 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21189 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq21189
       grind)
    | exact resolve eq13 eq21189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21247 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21230
  have eq21659 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq20873 eq1019
    | (have j0 := eq1019 (σ y) (σ x)
       grind)
    | (have r₁ := eq1019 (σ y) (σ x)
       have r₂ := eq20873
       grind)
    | exact resolve eq1019 eq20873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019 eq20873
  have eq21660 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (k (M.op x y) x) := by grind
  clear eq21659
  have eq21664 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq26 eq21660
    | exact resolve eq21660 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21660
  have eq24425 : (σ (M.op x y)) = (k (σ (k (M.op x y) x)) (k (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6144 eq19721
    | exact resolve eq19721 eq6144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19721
  have eq24523 : (σ (M.op x y)) = (k (k (σ (M.op x y)) (σ x)) (k (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24425
       have i₂ := eq39 sF0
       grind)
    | exact superpose eq39 eq24425
    | exact resolve eq24425 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24425
  have eq24551 : (σ (M.op x y)) = (k (k (σ (M.op x y)) (σ x)) (k (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq24523
    | exact resolve eq24523 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24523
  have eq24573 : (σ y) = (k (k (σ y) (σ x)) (k (σ y) (σ x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19702 eq24551
    | exact resolve eq24551 eq19702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24551
  have eq26239 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq21664 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq21664
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq21664
       grind)
    | exact resolve eq12 eq21664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21664
  have eq26261 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by grind
  clear eq26239
  have eq26274 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq26 eq26261
    | exact resolve eq26261 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26261
  have eq26275 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by grind
  clear eq26274
  have eq26960 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq26275 eq24573
    | exact resolve eq24573 eq26275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24573
  have eq26963 : (τ (σ y)) = (k (τ (σ y)) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq26275 eq141
    | exact resolve eq141 eq26275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26275
  have eq26972 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq31 eq26963
    | exact resolve eq26963 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26963
  have eq26975 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq19992 eq26960
    | exact resolve eq26960 eq19992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19992 eq26960
  have eq26977 : (M.op x y) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq26972
       have i₂ := eq19677
       grind)
    | exact superpose eq19677 eq26972
    | exact resolve eq26972 eq19677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26972
  have eq26980 : x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | (have r₁ := eq26975
       have r₂ := eq11079
       grind)
    | exact resolve eq26975 eq11079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26975
  have eq26984 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq11040 eq26980
    | exact resolve eq26980 eq11040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11040 eq26980
  have eq26987 : x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq26984
       have r₂ := eq11079
       grind)
    | exact resolve eq26984 eq11079
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11079 eq26984
  have eq26999 : (M.op x y) = (k x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26987 eq6144
    | exact resolve eq6144 eq26987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6144
  have eq27017 : x ≠ x ∨ (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26987 eq20062
    | (have r₁ := eq20062
       have r₂ := eq26987
       grind)
    | exact resolve eq20062 eq26987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27034 : (M.op x y) = (k x (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq27017
  have eq27045 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq26999
  have eq28082 : x ≠ (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq26977 eq20062
    | (have r₁ := eq20062
       have r₂ := eq26977
       grind)
    | exact resolve eq20062 eq26977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28099 : x ≠ (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by grind
  clear eq26977
  have eq28107 : x = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq28099
       have r₂ := eq26987
       grind)
    | exact resolve eq28099 eq26987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26987 eq28099
  have eq28121 : (M.op x y) = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k (M.op x y) x) := by
    first
    | (have r₁ := eq28082
       have r₂ := eq27034
       grind)
    | exact resolve eq28082 eq27034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27034 eq28082
  have eq28133 : (M.op x y) = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq28121
       have r₂ := eq20062
       grind)
    | exact resolve eq28121 eq20062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20062 eq28121
  have eq28163 : (M.op x y) = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28107 eq20041
    | exact resolve eq20041 eq28107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28107
  have eq28240 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28133 eq35
    | exact resolve eq35 eq28133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq28133
  have eq28254 : (σ (M.op x y)) = (k (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq28240
    | exact resolve eq28240 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28240
  have eq28269 : (σ y) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19702 eq28254
    | exact resolve eq28254 eq19702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28254
  have eq28305 : x ≠ (M.op x y) ∨ (M.op x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq28163
       grind)
    | exact superpose eq28163 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq28163
       grind)
    | exact resolve eq13 eq28163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28163
  have eq28342 : (M.op x y) = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq28305
       have r₂ := eq27045
       grind)
    | exact resolve eq28305 eq27045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28305
  have eq28472 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28269 eq1048
    | (have j0 := eq1048 (σ x) (σ y)
       grind)
    | exact resolve eq1048 eq28269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1048 eq28269
  have eq28474 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28472
  have eq28483 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq28474
    | exact resolve eq28474 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq28474
  have eq28484 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28483
  have eq28531 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq28342
       grind)
    | exact superpose eq28342 eq39
    | exact resolve eq39 eq28342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq28342
  have eq28547 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28531
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28531
    | exact resolve eq28531 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28531
  have eq28550 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq28547
    | exact resolve eq28547 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq28547
  have eq28553 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19702 eq28550
    | exact resolve eq28550 eq19702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28550
  have eq28557 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21247 eq28553
    | exact resolve eq28553 eq21247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21247
  have eq28559 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq28553 eq1021
    | exact resolve eq1021 eq28553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1021 eq28553
  have eq28579 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq21189 eq28559
    | exact resolve eq28559 eq21189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28559
  have eq28581 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq28557
       have r₂ := eq28484
       grind)
    | exact resolve eq28557 eq28484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28484 eq28557
  have eq28586 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq21189 eq28579
    | (have j0 := eq28579 X0
       grind)
    | exact resolve eq28579 eq21189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21189 eq28579
  have eq28588 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20812 eq28581
    | exact resolve eq28581 eq20812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20812 eq28581
  have eq28589 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq28588
  have eq28593 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ y)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq28586 X0
       grind)
    | (have r₁ := eq28586 X0
       have r₂ := eq20187
       grind)
    | exact resolve eq28586 eq20187
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20187 eq28586
  have eq28598 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq28589 eq27
    | exact resolve eq27 eq28589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq28606 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28589 eq888
    | exact resolve eq888 eq28589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888 eq28589
  have eq28621 : (σ x) ≠ (σ y) := by
    first
    | exact superpose eq19702 eq28598
    | exact resolve eq28598 eq19702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19702 eq28598
  have eq28640 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq28606 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq28606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28662 : (σ x) = (k (M.op (σ x) (σ x)) (M.op (M.op (σ x) (σ x)) (σ x))) := by
    first
    | exact superpose eq28606 eq3906
    | exact resolve eq3906 eq28606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3906
  have eq28663 : (σ x) = (k (M.op (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq28662
       have i₂ := eq850 sF2 sF2
       grind)
    | exact superpose eq850 eq28662
    | exact resolve eq28662 eq850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28662
  have eq28674 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq28640
       have r₂ := eq28621
       grind)
    | exact resolve eq28640 eq28621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28640
  have eq28700 : (τ (σ x)) = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | exact superpose eq28663 eq141
    | exact resolve eq141 eq28663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq28663
  have eq28705 : x = (k (τ (M.op (σ x) (σ x))) x) := by
    first
    | exact superpose eq29 eq28700
    | exact resolve eq28700 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28700
  have eq29031 : (τ (σ x)) = (k (M.op x y) (τ (σ x))) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq28674 eq19737
    | exact resolve eq19737 eq28674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19737 eq28674
  have eq29045 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq29 eq29031
    | exact resolve eq29031 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29031
  have eq29099 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq29045 eq850
    | exact resolve eq850 eq29045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29045
  have eq29141 : x = (k (τ (σ y)) x) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq29099 eq28705
    | exact resolve eq28705 eq29099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29099
  have eq29199 : x = (k y x) ∨ x = (k (M.op x y) x) := by
    first
    | exact superpose eq31 eq29141
    | exact resolve eq29141 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq29141
  have eq29215 : x = (k (M.op x y) x) ∨ x = (k (M.op x y) x) := by
    first
    | (have i₁ := eq29199
       have i₂ := eq19677
       grind)
    | exact superpose eq19677 eq29199
    | exact resolve eq29199 eq19677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19677 eq29199
  have eq29216 : x = (k (M.op x y) x) := by grind
  clear eq29215
  have eq29952 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq29216 eq20041
    | exact resolve eq20041 eq29216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20041 eq29216
  have eq30025 : x ≠ (M.op x y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq29952
       grind)
    | exact superpose eq29952 eq13
    | exact resolve eq13 eq29952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29952
  have eq30060 : (M.op x y) = (k x x) := by
    first
    | (have r₁ := eq30025
       have r₂ := eq27045
       grind)
    | exact resolve eq30025 eq27045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27045 eq30025
  have eq31085 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq28593 eq850
    | exact resolve eq850 eq28593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850 eq28593
  have eq31199 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq31085 eq28606
    | exact resolve eq28606 eq31085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28606 eq31085
  have eq31229 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq31199
  have eq31268 : x = (k (τ (σ x)) x) := by
    first
    | exact superpose eq31229 eq28705
    | exact resolve eq28705 eq31229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28705 eq31229
  have eq31323 : x = (k x x) := by
    first
    | exact superpose eq29 eq31268
    | exact resolve eq31268 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq31268
  have eq31340 : x = (M.op x y) := by
    first
    | (have i₁ := eq31323
       have i₂ := eq30060
       grind)
    | exact superpose eq30060 eq31323
    | exact resolve eq31323 eq30060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30060 eq31323
  have eq31344 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq31340
       grind)
    | exact superpose eq31340 eq22
    | exact resolve eq22 eq31340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq31340
  have eq31517 : (σ x) = (σ y) := by
    first
    | exact superpose eq31344 eq19688
    | exact resolve eq19688 eq31344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19688 eq31344
  have eq31586 : False := by grind
  exact eq31586

/-- `Equation1874`: `x = (x ◇ (y ◇ z)) ◇ (y ◇ w)`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(X,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_y_pxy_x_pyx_Equation1874 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1874 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1874.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X1 X3)) = X0 := by
    intro X0 X1 X2 X3
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
  have eq51 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op x X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 x y X1
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y X1
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 X5 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X2 X3)) X5)) = X1 := by
    intro X0 X1 X2 X3 X5
    first
    | (have i₁ := eq14 X1 (M.op X0 (M.op X2 X3)) (M.op X2 x) X5
       have i₂ := eq14 X0 X2 X3 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X1 X4)) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14 (M.op X0 (M.op X1 X4)) X1 x X2
       have i₂ := eq14 X0 X1 X4 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X1)) X0) = (M.op (M.op X0 (M.op X0 X1)) X0) := by
    intro X0 X1
    grind
  have eq74 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq77 : y ≠ (M.op x y) ∨ y = (M.op x x) ∨ x = (k x y) := by
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
  have eq79 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) ≠ X0 ∨ (M.op X1 X3) = (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) ∨ (M.op X0 (M.op X1 X2)) = (k (M.op X0 (M.op X1 X2)) (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 (M.op X0 (M.op X1 X2)) (M.op X1 X3)
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X0 (M.op X1 X2)) (M.op X1 X3)
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 X3) (M.op X1 X2)) (M.op X1 X3)
       have r₂ := eq14 (M.op X1 X3) X1 X2 X3
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
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
  have eq103 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
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
  have eq104 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq104
  have eq114 : (k (σ x) (σ y)) = (σ (M.op y x)) ∨ y = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq103
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq103
    | exact resolve eq103 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq102
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq102
    | exact resolve eq102 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq115
    | exact resolve eq115 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq120 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq89
       have i₂ := eq11 sF3 sF3
       grind)
    | exact superpose eq11 eq89
    | (have j1 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq89 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : (k y y) = (τ (M.op (σ y) (σ y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq120
  have eq125 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq38 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq38
    | exact resolve eq38 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
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
  have eq134 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq143 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq132 eq16
    | exact resolve eq16 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq157 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq134 eq16
    | exact resolve eq16 eq134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq178 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq157
       have i₂ := eq11 sF1 sF1
       grind)
    | exact superpose eq11 eq157
    | (have j1 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq157 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq180 : (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq178
  have eq212 : ∀ X0 X2 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op x X2)) := by
    intro X0 X2
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq52
    | (have j0 := eq52 X0 (σ y)
       grind)
    | exact resolve eq52 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq222 : ∀ X0 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op (σ x) X2)) := by
    intro X0 X2
    first
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq409 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X2))) = (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X2))) := by
    intro X0 X1 X2
    grind
  have eq495 : ∀ X0 X1 X2 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op X0 X1)) X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ y) (σ x) X0 X1 X2
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq518 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1 x x (M.op x x)
       have i₂ := eq14 X0 x x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 (M.op (M.op X0 X2) X3)) X0) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X1 (M.op X0 X2) X3 (M.op (M.op X2 (M.op x x)) x)
       have i₂ := eq53 X2 X0 x x x
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq535 : ∀ X0 X1 X2 X6 : G, (M.op X1 X0) = (M.op X1 (M.op (M.op X0 X2) X6)) := by
    intro X0 X1 X2 X6
    first
    | (have i₁ := eq54 X1 (M.op X0 X2) (M.op (M.op X2 (M.op x x)) x) X6
       have i₂ := eq53 X2 X0 x x x
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq549 : x = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq518 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq518
    | (have j0 := eq518 y x
       grind)
    | exact resolve eq518 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq518
    | (have j0 := eq518 (σ y) (σ x)
       grind)
    | exact resolve eq518 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq582 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) X1)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq550 eq14
    | exact resolve eq14 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) X0) (M.op X0 X1)) = (M.op (M.op (M.op X0 X1) X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq67 (M.op X1 X0) (M.op (M.op X0 (M.op x x)) x)
       have i₂ := eq53 X0 X1 x x x
       grind)
    | exact superpose eq53 eq67
    | exact resolve eq67 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq727 : ∀ X0 X1 X2 X3 X4 : G, (σ X1) = (M.op (σ (k X0 X1)) (M.op (M.op (σ X0) (M.op X2 X3)) X4)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (σ X0) (σ X1) X2 X3 X4
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq53
    | (have j1 := eq95 X0 X1
       grind)
    | exact resolve eq53 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq95
  have eq913 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op (M.op X0 X1) (M.op X0 X2))) ∨ (M.op (M.op X0 X1) (M.op X0 X2)) = (k (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq79 (M.op X0 X1) X0 X2 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq2134 : ∀ X0 X2 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq495 (M.op X0 x) x X2
       have i₂ := eq518 x X0
       grind)
    | exact superpose eq518 eq495
    | exact resolve eq495 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq6459 : ∀ X0 X1 X2 : G, (k (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X2))) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq409 X0 X1 X2
       have i₂ := eq535 X0 (M.op X0 X1) X1 (M.op X0 X2)
       grind)
    | exact superpose eq535 eq409
    | exact resolve eq409 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409
  have eq9882 : ∀ X0 X1 : G, (σ X1) = (M.op (σ (k X0 X1)) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq727 X0 X1 x x x
       have i₂ := eq535 (σ X0) (σ (k X0 X1)) (M.op x x) x
       grind)
    | exact superpose eq535 eq727
    | (have j0 := eq727 X0 X1 x x x
       grind)
    | exact resolve eq727 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq727
  have eq10074 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq9882 y y
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq9882
    | (have j0 := eq9882 y y
       grind)
    | exact resolve eq9882 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq10076 : ∀ X0 : G, (σ (τ X0)) = (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq125 eq9882
    | (have j0 := eq9882 (M.op x y) (τ X0)
       grind)
    | exact resolve eq9882 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq10212 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq10074
  have eq10240 : ∀ X0 : G, (σ (τ X0)) = (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) ∨ (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10076
    | (have j0 := eq10076 X0
       grind)
    | exact resolve eq10076 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10076
  have eq10242 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq10212
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10212
    | exact resolve eq10212 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10212
  have eq10332 : ∀ X0 : G, (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 ∨ (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq10240 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10240
    | (have j0 := eq10240 X0
       grind)
    | exact resolve eq10240 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10240
  have eq10334 : (σ y) = (M.op (k (σ y) (σ y)) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq10242
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10242
    | exact resolve eq10242 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10242
  have eq10420 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 ∨ (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq10332 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10332
    | (have j0 := eq10332 X0
       grind)
    | exact resolve eq10332 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10332
  have eq10506 : ∀ X0 : G, (M.op (σ (M.op x y)) X0) = X0 ∨ (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 ∨ (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq10420
    | (have j0 := eq10420 X0
       grind)
    | exact resolve eq10420 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10420
  have eq10588 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq21 eq10506
    | (have j0 := eq10506 X0
       grind)
    | exact resolve eq10506 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10506
  have eq10670 : ∀ X0 : G, (M.op (k (σ (M.op x y)) X0) (σ (M.op x y))) = X0 ∨ (M.op (σ (M.op x y)) X0) = X0 ∨ (M.op (σ (M.op x y)) (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq10588 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10588
    | (have j0 := eq10588 X0
       grind)
    | exact resolve eq10588 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10588
  have eq14244 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X2)) = (k (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq913 X0 X1 X2
       have i₂ := eq535 X0 (M.op (M.op X0 X1) (M.op X0 X2)) X1 (M.op X0 X2)
       grind)
    | exact superpose eq535 eq913
    | (have j0 := eq913 X0 X1 X2
       grind)
    | exact resolve eq913 eq535
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq14317 : x = (k x (M.op x (M.op x y))) ∨ (M.op x x) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq51 eq14244
    | exact resolve eq14244 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq14319 : (σ x) = (k (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq52 eq14244
    | exact resolve eq14244 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14244
  have eq23394 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq116 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq23401 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq23394
    | exact resolve eq23394 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23394
  have eq23412 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq23401
       have r₂ := eq28
       grind)
    | exact resolve eq23401 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23401
  have eq23434 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23412 eq518
    | exact resolve eq518 eq23412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23412
  have eq23447 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq23434
    | exact resolve eq23434 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23434
  have eq23459 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23447 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq23447
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq23447
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq23447
       grind)
    | exact resolve eq12 eq23447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23447
  have eq23485 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq23459
  have eq27289 : (τ (σ y)) = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23485 eq84
    | exact resolve eq84 eq23485
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq23485
  have eq27319 : y = (k y x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq30 eq27289
    | exact resolve eq27289 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27289
  have eq27322 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq27319
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq27319
       have r₂ := eq12 y x
       grind)
    | exact resolve eq27319 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27319
  have eq27351 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27322 eq518
    | exact resolve eq518 eq27322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27322
  have eq27372 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq27351
    | exact resolve eq27351 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27351
  have eq27373 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq27372
  have eq27405 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq27373
       grind)
    | exact superpose eq27373 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq27373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27373
  have eq27414 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq27405
  have eq27422 : x = (M.op y y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27414
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq27414
    | exact resolve eq27414 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27414
  have eq27635 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq518 y y
       have i₂ := eq27422
       grind)
    | exact superpose eq27422 eq518
    | exact resolve eq518 eq27422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27422
  have eq27648 : y = (M.op x y) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27635
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq27635
    | exact resolve eq27635 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27635
  have eq27649 : x = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq27648
  have eq27666 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op y X1)) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 y x X1
       have i₂ := eq27649
       grind)
    | exact superpose eq27649 eq14
    | exact resolve eq14 eq27649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27682 : y = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq518 x y
       have i₂ := eq27649
       grind)
    | exact superpose eq27649 eq518
    | exact resolve eq518 eq27649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27684 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x X1)) y) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq534 y X0 x X1
       have i₂ := eq27649
       grind)
    | exact superpose eq27649 eq534
    | exact resolve eq534 eq27649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq27685 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq535 y X0 x X1
       have i₂ := eq27649
       grind)
    | exact superpose eq27649 eq535
    | exact resolve eq535 eq27649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq535
  have eq27686 : (M.op (M.op x y) x) = (k (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq665 y x
       have i₂ := eq27649
       grind)
    | exact superpose eq27649 eq665
    | exact resolve eq665 eq27649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27649
  have eq27693 : (M.op (M.op x y) x) = (k (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27686
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq27686
    | exact resolve eq27686 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27686
  have eq27694 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq27685 X0 x
       have i₂ := eq212 X0 x
       grind)
    | (have i₁ := eq27685 X0 y
       have i₂ := eq212 X0 x
       grind)
    | exact superpose eq212 eq27685
    | (have j0 := eq27685 X0 y
       grind)
    | exact resolve eq27685 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27685
  have eq27695 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) y) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq27684 X0 x
       have i₂ := eq212 X0 x
       grind)
    | (have i₁ := eq27684 X0 y
       have i₂ := eq212 X0 x
       grind)
    | exact superpose eq212 eq27684
    | (have j0 := eq27684 X0 y
       grind)
    | exact resolve eq27684 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212 eq27684
  have eq27754 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  have eq27793 : (M.op x y) = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27754
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq27754
    | exact resolve eq27754 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27754
  have eq27901 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq27793
       grind)
    | exact superpose eq27793 eq45
    | exact resolve eq45 eq27793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq27918 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq9882 x y
       have i₂ := eq27793
       grind)
    | exact superpose eq27793 eq9882
    | (have j0 := eq9882 x y
       grind)
    | exact resolve eq9882 eq27793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27793
  have eq27921 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27918
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27918
    | exact resolve eq27918 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27918
  have eq27935 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq27901
    | exact resolve eq27901 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27901
  have eq27936 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq27921
    | exact resolve eq27921 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27921
  have eq27942 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27936
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq27936
    | exact resolve eq27936 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27936
  have eq27948 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27942
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq27942
    | exact resolve eq27942 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27942
  have eq27954 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27948
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27948
    | exact resolve eq27948 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27948
  have eq27963 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq27954
    | exact resolve eq27954 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27954
  have eq27964 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq27963
  have eq27970 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq27964
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27964
    | exact resolve eq27964 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27964
  have eq27976 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq27970
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq27970
    | exact resolve eq27970 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27970
  have eq28263 : x = (k x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27694 eq14317
    | exact resolve eq14317 eq27694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14317 eq27694
  have eq28311 : x = (k x (M.op x y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28263
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28263
    | exact resolve eq28263 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28263
  have eq28331 : (M.op x y) = (M.op x x) ∨ x = (k x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq28311
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28311
    | exact resolve eq28311 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28311
  have eq29263 : ∀ X0 : G, x = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq27666 x X0
       have i₂ := eq27682
       grind)
    | exact superpose eq27682 eq27666
    | exact resolve eq27666 eq27682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27666
  have eq29333 : ∀ X0 : G, x = (M.op y (M.op y X0)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq29263 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29263
  have eq30740 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (k x (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq27682
       have i₂ := eq28331
       grind)
    | exact superpose eq28331 eq27682
    | exact resolve eq27682 eq28331
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27682 eq28331
  have eq30776 : x = (k x (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq30740
  have eq30809 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30776 eq9882
    | (have j0 := eq9882 x (M.op x y)
       grind)
    | exact resolve eq9882 eq30776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9882 eq30776
  have eq30810 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq30809
  have eq30812 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq30810
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30810
    | exact resolve eq30810 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30810
  have eq30827 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq30812
    | exact resolve eq30812 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30812
  have eq30833 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq30827
    | exact resolve eq30827 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30827
  have eq30839 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq30833
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq30833
    | exact resolve eq30833 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30833
  have eq31885 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq27976
  have eq31925 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq31885
    | exact resolve eq31885 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31885
  have eq32204 : (σ x) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30839 eq518
    | exact resolve eq518 eq30839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32394 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31925 eq27935
    | exact resolve eq27935 eq31925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27935 eq31925
  have eq32402 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ (M.op x y)) (σ x)) := by grind
  clear eq32394
  have eq32411 : (σ y) = (M.op (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq32402
       have r₂ := eq28
       grind)
    | exact resolve eq32402 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32402
  have eq32471 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32411 eq518
    | exact resolve eq518 eq32411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32491 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq32471 eq2134
    | exact resolve eq2134 eq32471
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2134 eq32471
  have eq32707 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ (M.op x y)) X1)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X1
    first
    | exact superpose eq32491 eq14
    | exact resolve eq14 eq32491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32491
  have eq39466 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32204 eq32707
    | exact resolve eq32707 eq32204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32204 eq32707
  have eq39497 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq39466
  have eq49580 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq39497 eq30839
    | exact resolve eq30839 eq39497
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30839 eq39497
  have eq49617 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq49580
  have eq49636 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq49617
       have r₂ := eq28
       grind)
    | exact resolve eq49617 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49617
  have eq49665 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49636 eq518
    | exact resolve eq518 eq49636
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49636
  have eq49980 : (M.op (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq49665
  have eq53689 : (τ (M.op (σ (M.op x y)) (σ x))) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq49980 eq143
    | exact resolve eq143 eq49980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143 eq49980
  have eq59779 : (τ (σ y)) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq32411 eq53689
    | exact resolve eq53689 eq32411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32411 eq53689
  have eq59917 : (τ (σ y)) = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq59779
  have eq59926 : y = (k (M.op x y) x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq30 eq59917
    | exact resolve eq59917 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59917
  have eq59938 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq59926 eq27693
    | exact resolve eq27693 eq59926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27693 eq59926
  have eq59946 : y = (M.op (M.op x y) x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq59938
  have eq60301 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq59946 eq518
    | exact resolve eq518 eq59946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59946
  have eq60646 : x = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq29333 x
       have i₂ := eq60301
       grind)
    | exact superpose eq60301 eq29333
    | exact resolve eq29333 eq60301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29333 eq60301
  have eq60676 : x = (M.op y (M.op x y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq60646
  have eq61607 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq60676 eq27695
    | exact resolve eq27695 eq60676
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27695 eq60676
  have eq61634 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq61607
  have eq61653 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq61634
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq61634
    | exact resolve eq61634 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61634
  have eq61654 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq61653
  have eq61666 : ∀ X0 X1 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) X1)) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq61654 eq52
    | exact resolve eq52 eq61654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq61675 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61654 eq550
    | exact resolve eq550 eq61654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq61676 : ∀ X0 X1 : G, (M.op (M.op X0 (σ x)) (M.op (σ y) X1)) = X0 ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq61654 eq582
    | exact resolve eq582 eq61654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq61692 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61654 eq14319
    | exact resolve eq14319 eq61654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14319
  have eq61709 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq61692
    | exact resolve eq61692 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61692
  have eq61718 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq222 eq61666
    | (have j0 := eq61666 X0 (σ y)
       grind)
    | exact resolve eq61666 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq61666
  have eq61719 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq61709
    | exact resolve eq61709 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61709
  have eq62001 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61675 eq122
    | exact resolve eq122 eq61675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq62048 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (M.op (σ y) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq61675 eq6459
    | exact resolve eq6459 eq61675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6459
  have eq62070 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (M.op (σ y) X0))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq27 eq62048
    | (have j0 := eq62048 X0
       grind)
    | exact resolve eq62048 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62048
  have eq62081 : x = (k y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq62001
    | exact resolve eq62001 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62001
  have eq63759 : (k (σ y) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq10334 eq61718
    | exact resolve eq61718 eq10334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10334
  have eq63763 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61675 eq61718
    | exact resolve eq61718 eq61675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61675 eq61718
  have eq63831 : (σ y) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by grind
  clear eq63763
  have eq63883 : (σ x) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq63831 eq221
    | exact resolve eq221 eq63831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq63831
  have eq70712 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) ∨ y = (M.op x y) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq61719 eq61676
    | exact resolve eq61676 eq61719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61676 eq61719
  have eq70746 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) ∨ y = (M.op x y) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq70712 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70712
  have eq74537 : (k y y) = (τ (M.op (σ y) (M.op (σ x) (σ y)))) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq63759 eq89
    | exact resolve eq89 eq63759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63759
  have eq75894 : ∀ X1 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ y) X1)) ∨ y = (M.op x y) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    intro X1
    first
    | exact superpose eq70746 eq14
    | exact resolve eq14 eq70746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70746
  have eq84726 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq75894 eq62070
    | exact resolve eq62070 eq75894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62070 eq75894
  have eq84786 : (M.op (σ x) (σ y)) = (k (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq84726
  have eq84834 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq61654 eq84786
    | exact resolve eq84786 eq61654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61654 eq84786
  have eq84857 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq84834
  have eq84868 : (τ (σ y)) = (k x y) ∨ y = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq84857 eq61
    | exact resolve eq61 eq84857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84857
  have eq84929 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq30 eq84868
    | exact resolve eq84868 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84868
  have eq84944 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) ∨ y = (k x y) := by
    first
    | exact superpose eq84929 eq61
    | exact resolve eq61 eq84929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84929
  have eq85003 : y = (k x y) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | exact superpose eq29 eq84944
    | exact resolve eq84944 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84944
  have eq85038 : y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq85003
       grind)
    | exact superpose eq85003 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq85003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85003
  have eq85064 : y = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (k x y) := by
    first
    | (have r₁ := eq85038
       have r₂ := eq77
       grind)
    | exact resolve eq85038 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85038
  have eq85088 : y = (M.op y x) ∨ y = (M.op x x) ∨ x = (k x y) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq85064
       have r₂ := eq12 x y
       grind)
    | exact resolve eq85064 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85064
  have eq96720 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ y = (M.op x x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq114
       have i₂ := eq85088
       grind)
    | exact superpose eq85088 eq114
    | exact resolve eq114 eq85088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq85088
  have eq96758 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x x) ∨ x = (k x y) := by grind
  clear eq96720
  have eq96770 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (k x y) := by
    first
    | (have r₁ := eq96758
       have r₂ := eq77
       grind)
    | exact resolve eq96758 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96758
  have eq96773 : (σ y) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ x = (k x y) := by
    first
    | (have i₁ := eq96770
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq96770
    | exact resolve eq96770 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96770
  have eq114855 : (τ (σ y)) = (k x y) ∨ y = (M.op x x) ∨ x = (k x y) := by
    first
    | exact superpose eq96773 eq61
    | exact resolve eq61 eq96773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq96773
  have eq114925 : y = (k x y) ∨ y = (M.op x x) ∨ x = (k x y) := by
    first
    | exact superpose eq30 eq114855
    | exact resolve eq114855 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114855
  have eq116926 : x ≠ y ∨ y = (M.op x x) ∨ x = (k x y) := by grind
  clear eq114925
  have eq141496 : (τ (σ x)) = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq63883 eq74537
    | exact resolve eq74537 eq63883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63883 eq74537
  have eq141743 : (τ (σ x)) = (k y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq141496
  have eq141754 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq29 eq141743
    | exact resolve eq141743 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141743
  have eq141836 : (M.op (M.op (σ y) (σ y)) (σ y)) = (k (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq141754 eq665
    | exact resolve eq665 eq141754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq141883 : (σ y) = (k (M.op (σ y) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq141836
       have i₂ := eq518 sF3 sF3
       grind)
    | exact superpose eq518 eq141836
    | exact resolve eq141836 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141836
  have eq149567 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq141754 eq141883
    | exact resolve eq141883 eq141754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141754 eq141883
  have eq149584 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (k y y) := by grind
  clear eq149567
  have eq149600 : (τ (σ y)) = (k y y) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq149584 eq89
    | exact resolve eq89 eq149584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq149584
  have eq149703 : y = (k y y) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | exact superpose eq30 eq149600
    | exact resolve eq149600 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149600
  have eq149707 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq149703
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq149703
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq149703 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149748 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op x y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq149703
       grind)
    | exact superpose eq149703 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq149703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq149755 : x ≠ y ∨ y = (M.op x y) ∨ x = (k y y) := by grind
  clear eq149703
  have eq149762 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (k y y) := by grind
  clear eq149748
  have eq149779 : y = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq149707
  have eq149863 : (k y y) = (M.op y y) ∨ y = (M.op x y) ∨ x = (k y y) := by grind
  clear eq149762
  have eq149940 : (k y y) = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq149779
  have eq153911 : x ≠ (M.op y y) ∨ y = (M.op x y) ∨ x = (k y y) := by grind
  clear eq149863
  have eq155538 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq62081
       have i₂ := eq149940
       grind)
    | exact superpose eq149940 eq62081
    | exact resolve eq62081 eq149940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62081
  have eq155586 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq155538
  have eq155690 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq518 y y
       have i₂ := eq155586
       grind)
    | exact superpose eq155586 eq518
    | exact resolve eq518 eq155586
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155586
  have eq155727 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq155690
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq155690
    | exact resolve eq155690 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155690
  have eq155728 : (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq155727
  have eq156415 : y = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq155728 eq30
    | exact resolve eq30 eq155728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq155728
  have eq156950 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq156415
    | exact resolve eq156415 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq156415
  have eq158296 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq156950 eq21
    | exact resolve eq21 eq156950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq158303 : y ≠ y ∨ y = (M.op x x) ∨ x = (k x y) ∨ x = y := by
    first
    | exact superpose eq156950 eq77
    | (have r₁ := eq77
       have r₂ := eq156950
       grind)
    | exact resolve eq77 eq156950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq158360 : x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq156950 eq549
    | exact resolve eq549 eq156950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549 eq156950
  have eq158496 : y = (M.op x x) ∨ x = (k x y) ∨ x = y := by grind
  clear eq158303
  have eq158640 : y = (M.op x x) ∨ x = (k x y) := by
    first
    | (have r₁ := eq158496
       have r₂ := eq116926
       grind)
    | exact resolve eq158496 eq116926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116926 eq158496
  have eq158647 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq158296
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq158296
    | exact resolve eq158296 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158296
  have eq163988 : (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq111
       have i₂ := eq158360
       grind)
    | exact superpose eq158360 eq111
    | exact resolve eq111 eq158360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq163991 : x ≠ x ∨ y = (M.op x y) ∨ x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq153911
       have i₂ := eq158360
       grind)
    | exact superpose eq158360 eq153911
    | (have r₁ := eq153911
       have r₂ := eq158360
       grind)
    | exact resolve eq153911 eq158360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153911 eq158360
  have eq164051 : y = (M.op x y) ∨ x = (k y y) ∨ x = y := by grind
  clear eq163991
  have eq164053 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by grind
  clear eq163988
  have eq164073 : x = (k y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq164051
       have r₂ := eq149755
       grind)
    | exact resolve eq164051 eq149755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149755 eq164051
  have eq164074 : (σ x) = (k (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq164053
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq164053
    | exact resolve eq164053 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164053
  have eq172392 : x = (M.op y y) ∨ y = (M.op x y) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq149940
       have i₂ := eq164073
       grind)
    | exact superpose eq164073 eq149940
    | exact resolve eq149940 eq164073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149940 eq164073
  have eq172426 : x = (M.op y y) ∨ y = (M.op x y) := by grind
  clear eq172392
  have eq172503 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq158647 eq164074
    | exact resolve eq164074 eq158647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158647 eq164074
  have eq172571 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq172503
  have eq173022 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq518 y y
       have i₂ := eq172426
       grind)
    | exact superpose eq172426 eq518
    | exact resolve eq518 eq172426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172426
  have eq173059 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq173022
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq173022
    | exact resolve eq173022 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173022
  have eq173060 : y = (M.op x y) := by grind
  clear eq173059
  have eq173075 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq173060 eq21
    | exact resolve eq21 eq173060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq173437 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq173075
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq173075
    | exact resolve eq173075 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173075
  have eq173448 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq173437 eq27
    | exact resolve eq27 eq173437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq174291 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq172571 eq10670
    | (have j0 := eq10670 (σ (M.op x y))
       grind)
    | exact resolve eq10670 eq172571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10670
  have eq174321 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq174291
  have eq174325 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq173448 eq174321
    | exact resolve eq174321 eq173448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174321
  have eq174336 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq174325
       have r₂ := eq28
       grind)
    | exact resolve eq174325 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174325
  have eq175579 : (k (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq174336
  have eq193685 : (M.op x y) = (k x y) ∨ x = (k x y) := by grind
  clear eq158640
  have eq193738 : (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq193685
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq193685
    | exact resolve eq193685 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq193685
  have eq193763 : y = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq173060 eq193738
    | exact resolve eq193738 eq173060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193738
  have eq197554 : x ≠ y ∨ x = (k x y) := by grind
  clear eq193763
  have eq199920 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq175579 eq172571
    | exact resolve eq172571 eq175579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172571 eq175579
  have eq199952 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq199920
  have eq200043 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq199952 eq518
    | exact resolve eq518 eq199952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518 eq199952
  have eq200073 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq173448 eq200043
    | exact resolve eq200043 eq173448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200043
  have eq200089 : x = y := by
    first
    | (have r₁ := eq200073
       have r₂ := eq28
       grind)
    | exact resolve eq200073 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200073
  have eq200104 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq200089
       grind)
    | exact superpose eq200089 eq25
    | exact resolve eq25 eq200089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq200383 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq197554
       have i₂ := eq200089
       grind)
    | exact superpose eq200089 eq197554
    | (have r₁ := eq197554
       have r₂ := eq200089
       grind)
    | exact resolve eq197554 eq200089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197554
  have eq200387 : x = (k x x) := by grind
  clear eq200383
  have eq200676 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq173437 eq200104
    | exact resolve eq200104 eq173437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173437 eq200104
  have eq200899 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq200676
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq200676
    | exact resolve eq200676 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200676
  have eq203192 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq200899 eq173448
    | exact resolve eq173448 eq200899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173448
  have eq207032 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq203192 eq180
    | exact resolve eq180 eq203192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180 eq203192
  have eq207127 : (τ (M.op (σ x) (σ y))) = (k (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq207032
       have r₂ := eq28
       grind)
    | exact resolve eq207032 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207032
  have eq207147 : (k y y) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq173060 eq207127
    | exact resolve eq207127 eq173060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173060 eq207127
  have eq207158 : (k x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq207147
       have i₂ := eq200089
       grind)
    | exact superpose eq200089 eq207147
    | exact resolve eq207147 eq200089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200089 eq207147
  have eq207167 : x = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq207158
       have i₂ := eq200387
       grind)
    | exact superpose eq200387 eq207158
    | exact resolve eq207158 eq200387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200387 eq207158
  have eq208384 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq207167 eq15
    | exact resolve eq15 eq207167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207167
  have eq208990 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq208384
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq208384
    | exact resolve eq208384 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq208384
  have eq209204 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq200899 eq208990
    | exact resolve eq208990 eq200899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200899 eq208990
  have eq209321 : False := by grind
  exact eq209321

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_x_pyx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X0 X0)) = X0 := by
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
  have eq50 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq51 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ x) (σ y))) (M.op (σ x) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
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
  have eq59 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 (M.op X0 X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq75
    | exact resolve eq75 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq81 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq80
    | exact resolve eq80 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq81
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq81
    | exact resolve eq81 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq93 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq108 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 X1 X2 (M.op X0 X0)
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq58
    | exact resolve eq58 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq471 : ∀ X0 X1 X2 : G, (M.op X0 (σ x)) = (M.op (M.op X2 (M.op X1 (M.op (σ x) (σ y)))) (M.op (M.op X0 (σ x)) (M.op X0 (σ x)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq57 eq58
    | exact resolve eq58 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq58
  have eq592 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq70 X0 X1
       grind)
    | exact superpose eq70 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq70 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq70 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq70 X0 X1
       grind)
    | exact resolve eq12 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq599 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq602 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq592 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq610 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq602 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq602 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq602 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq602 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq618 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq610 X0 X1
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq610
    | (have j0 := eq610 X0 X1
       grind)
    | exact resolve eq610 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq3355 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq464 X0 X0 X1
       have i₂ := eq62 X0 X0
       grind)
    | exact superpose eq62 eq464
    | exact resolve eq464 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq464
  have eq3797 : ∀ X0 X1 : G, (M.op (σ x) (σ x)) = (M.op (M.op X0 (M.op X1 (M.op (σ x) (σ y)))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq471 sF2 X1 x
       have i₂ := eq62 sF2 sF2
       grind)
    | exact superpose eq62 eq471
    | exact resolve eq471 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq471
  have eq3951 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq3797 sF4 sF4
       have i₂ := eq59 sF4
       grind)
    | exact superpose eq59 eq3797
    | exact resolve eq3797 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3797
  have eq15180 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq82 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq15189 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq15180
    | exact resolve eq15180 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15180
  have eq15200 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq15189
       have r₂ := eq27
       grind)
    | exact resolve eq15189 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15189
  have eq15202 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq26 eq15200
    | exact resolve eq15200 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15200
  have eq15211 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq15202 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq15202
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq15202
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq15202
       grind)
    | exact resolve eq13 eq15202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15202
  have eq15231 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq15211
  have eq15350 : (τ (σ x)) = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq15231 eq55
    | exact resolve eq55 eq15231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq15231
  have eq15380 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq28 eq15350
    | exact resolve eq15350 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq15350
  have eq15383 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq15380
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq15380
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq15380
       have r₂ := eq13 x y
       grind)
    | exact resolve eq15380 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15380
  have eq15392 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 x y
       have i₂ := eq15383
       grind)
    | exact superpose eq15383 eq11
    | (have j0 := eq11 x y
       grind)
    | exact resolve eq11 eq15383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15397 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq599 x y
       have i₂ := eq15383
       grind)
    | exact superpose eq15383 eq599
    | (have j0 := eq599 x y
       grind)
    | exact resolve eq599 eq15383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15383
  have eq15403 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15397
  have eq15404 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15392
  have eq15408 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15403
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15403
    | exact resolve eq15403 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15403
  have eq15410 : x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15404
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15404
    | exact resolve eq15404 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15404
  have eq15411 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15410
  have eq15423 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15408
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15408
    | exact resolve eq15408 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15408
  have eq15427 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15423
    | exact resolve eq15423 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15423
  have eq15428 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq15427
  have eq15432 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15428
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15428
    | exact resolve eq15428 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15428
  have eq15435 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15432
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15432
    | exact resolve eq15432 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15432
  have eq15563 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq15411
       grind)
    | exact superpose eq15411 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq15411
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15411
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq15411
       grind)
    | exact resolve eq12 eq15411
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15411
  have eq15585 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15563
  have eq15586 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15585
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15585
    | exact resolve eq15585 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15585
  have eq15587 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq15586
  have eq15588 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq15587
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq15587
    | exact resolve eq15587 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15587
  have eq15747 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq15435 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq15435
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq15435
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq15435
       grind)
    | exact resolve eq12 eq15435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15435
  have eq15769 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq15747
  have eq15770 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15769
    | exact resolve eq15769 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15769
  have eq15771 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq15770
  have eq15772 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq15771
    | exact resolve eq15771 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15771
  have eq15774 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq93
       have i₂ := eq15588
       grind)
    | exact superpose eq15588 eq93
    | exact resolve eq93 eq15588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq15588
  have eq15804 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq15774
    | exact resolve eq15774 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15774
  have eq16051 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15804 eq15772
    | exact resolve eq15772 eq15804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15772 eq15804
  have eq16061 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq16051
  have eq16063 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq16061
       have r₂ := eq27
       grind)
    | exact resolve eq16061 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16061
  have eq16075 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16063 eq51
    | (have r₁ := eq51
       have r₂ := eq16063
       grind)
    | exact resolve eq51 eq16063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq16063
  have eq16100 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq16075
  have eq16217 : (τ (σ y)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq16100 eq108
    | exact resolve eq108 eq16100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq16100
  have eq16251 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq16217
    | exact resolve eq16217 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq16217
  have eq16255 : y = (k y x) := by
    first
    | (have r₁ := eq16251
       have r₂ := eq50
       grind)
    | exact resolve eq16251 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq16251
  have eq16266 : y = (M.op y x) ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq16255
       grind)
    | exact superpose eq16255 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq16255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16271 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq599 y x
       have i₂ := eq16255
       grind)
    | exact superpose eq16255 eq599
    | (have j0 := eq599 y x
       grind)
    | exact resolve eq599 eq16255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq16273 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq618 y x
       have i₂ := eq16255
       grind)
    | exact superpose eq16255 eq618
    | (have j0 := eq618 y x
       grind)
    | exact resolve eq618 eq16255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618 eq16255
  have eq16275 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16273
  have eq16277 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16271
  have eq16278 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq16266
  have eq16280 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16275
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16275
    | exact resolve eq16275 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16275
  have eq16282 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16277
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16277
    | exact resolve eq16277 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16277
  have eq16284 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16278
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16278
    | exact resolve eq16278 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16278
  have eq16293 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16280
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16280
    | exact resolve eq16280 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16280
  have eq16295 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16282
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16282
    | exact resolve eq16282 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16282
  have eq16297 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16293
    | exact resolve eq16293 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16293
  have eq16299 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16295
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16295
    | exact resolve eq16295 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16295
  have eq16301 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16297
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16297
    | exact resolve eq16297 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq16297
  have eq16303 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16299
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16299
    | exact resolve eq16299 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16299
  have eq16305 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16301
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16301
    | exact resolve eq16301 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16301
  have eq16307 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16303
    | exact resolve eq16303 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16303
  have eq16309 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16305
    | exact resolve eq16305 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16305
  have eq16498 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16309 eq3951
    | exact resolve eq3951 eq16309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3951 eq16309
  have eq17214 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq3355 x y
       have i₂ := eq16284
       grind)
    | exact superpose eq16284 eq3355
    | exact resolve eq3355 eq16284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3355
  have eq22515 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq16498 eq16307
    | exact resolve eq16307 eq16498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16307 eq16498
  have eq22548 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22515
  have eq22630 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq22548 eq59
    | exact resolve eq59 eq22548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22548
  have eq22660 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq22630
    | exact resolve eq22630 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq22630
  have eq22661 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22660
  have eq22664 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq22661 eq27
    | exact resolve eq27 eq22661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq22661
  have eq25394 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16284
       have i₂ := eq17214
       grind)
    | exact superpose eq17214 eq16284
    | exact resolve eq16284 eq17214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16284 eq17214
  have eq25429 : y = (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq25394
  have eq25449 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq59 x
       have i₂ := eq25429
       grind)
    | exact superpose eq25429 eq59
    | exact resolve eq59 eq25429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq25429
  have eq25482 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq25449
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq25449
    | exact resolve eq25449 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq25449
  have eq25483 : x = (M.op x y) := by grind
  clear eq25482
  have eq25487 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq25483 eq20
    | exact resolve eq20 eq25483
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq25483
  have eq25641 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq25487
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq25487
    | exact resolve eq25487 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq25487
  have eq25665 : False := by grind
  exact eq25665

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(Y,X) = X then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_x_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq19 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
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
  have eq20 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq24 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq103 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19 (M.op X0 X0) X0 X1 X2
       have i₂ := eq20 X0
       grind)
    | exact superpose eq20 eq19
    | exact resolve eq19 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op (M.op X4 X1) (M.op X4 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X4 X1) X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq19 X1 X4 X0 X2
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0)
       have i₂ := eq39 X0 X0
       grind)
    | exact superpose eq39 eq20
    | (have j1 := eq39 X0 X0
       grind)
    | exact resolve eq20 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (M.op (σ X0) X2)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq39 X0 X0
       grind)
    | exact superpose eq39 eq9
    | (have j1 := eq39 X0 X0
       grind)
    | exact resolve eq9 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 X2 : G, (σ X2) = (M.op (M.op X1 (σ X0)) (M.op (σ X2) (σ X2))) ∨ (σ (k X0 X2)) = (M.op (σ X0) (σ X2)) ∨ (σ X2) = (M.op (σ X2) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X2) X1 (σ X0)
       have i₂ := eq39 X0 X2
       grind)
    | exact superpose eq39 eq9
    | (have j1 := eq39 X0 X2
       grind)
    | exact resolve eq9 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 : G, (σ X0) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq39 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq39 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq39 X0 X1
       grind)
    | exact resolve eq12 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq39 X0 X1
       grind)
    | exact superpose eq39 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq39 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq39 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq39 X1 X1
       grind)
    | exact resolve eq13 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq39 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq190 : ∀ X0 X1 : G, (σ X0) ≠ (σ X1) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq39 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq192 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq189 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189
  have eq195 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq177 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq196 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X1 (M.op (σ X0) X2)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq174 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq197 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq173 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq203 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq195 X0 X1
       have j1 := eq190 X1 X0
       grind)
    | (have r₁ := eq195 X0 X1
       have r₂ := eq190 X0 X1
       grind)
    | (have r₁ := eq195 X1 X0
       have r₂ := eq190 X0 X1
       grind)
    | exact resolve eq195 eq190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190 eq195
  have eq204 : ∀ X0 X1 : G, (σ X0) ≠ (σ X1) ∨ (σ X0) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq176 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq176 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq176 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq215 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq203 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq203
    | (have j0 := eq203 X0 X1
       grind)
    | exact resolve eq203 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq216 : ∀ X0 X1 : G, (σ X0) ≠ (σ X1) ∨ (σ X0) = (σ (k X0 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq204 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq204
    | (have j0 := eq204 X0 X1
       grind)
    | exact resolve eq204 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq381 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 X1 (M.op X0 X0)
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq37
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq382 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq37 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq19 X1 X1 X0 X2
       grind)
    | exact superpose eq19 eq37
    | exact resolve eq37 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq37
  have eq500 : ∀ X0 : G, (σ (τ X0)) = (M.op (σ (τ X0)) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq197 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq197
    | (have j0 := eq197 (τ X0)
       grind)
    | exact resolve eq197 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq511 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq500 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq500
    | (have j0 := eq500 X0
       grind)
    | exact resolve eq500 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq517 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq511 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq511
    | (have j0 := eq511 X0
       grind)
    | exact resolve eq511 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511
  have eq563 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq118 (M.op X0 X1) X0 X1 (M.op X0 X1) X2
       have i₂ := eq20 (M.op X0 X1)
       grind)
    | exact superpose eq20 eq118
    | exact resolve eq118 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq624 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq382 X2 X0 (k X0 X0) X1
       have i₂ := eq517 X0
       grind)
    | exact superpose eq517 eq382
    | (have j1 := eq517 X0
       grind)
    | exact resolve eq382 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq382 (M.op X0 X1) X0 X1 (M.op X0 X1)
       have i₂ := eq20 (M.op X0 X1)
       grind)
    | exact superpose eq20 eq382
    | exact resolve eq382 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (M.op (M.op X1 (M.op (σ (τ X0)) X2)) (k (σ (τ X0)) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq196 (τ X0) X1 X2
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq196
    | (have j0 := eq196 (τ X0) X1 X2
       grind)
    | exact resolve eq196 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq704 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 X0)) = X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq686 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq686
    | (have j0 := eq686 X0 X1 X2
       grind)
    | exact resolve eq686 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686
  have eq710 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq704 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq704
    | (have j0 := eq704 X0 X1 X2
       grind)
    | exact resolve eq704 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq722 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq639 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq639
    | exact resolve eq639 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq769 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq216 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq1185 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq103 X0 X1 (M.op X0 X0)
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq103
    | exact resolve eq103 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1209 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) = (M.op X0 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq103 X0 (M.op (M.op X0 X0) X1) X1
       have i₂ := eq24 (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq24 eq103
    | exact resolve eq103 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq1249 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X0) X1)) = (M.op X1 (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1209 X0 X1
       have i₂ := eq722 X1 (M.op X0 X0)
       grind)
    | exact superpose eq722 eq1209
    | exact resolve eq1209 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq1257 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1185 X0 X1
       have i₂ := eq722 X0 X1
       grind)
    | exact superpose eq722 eq1185
    | exact resolve eq1185 eq722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1185
  have eq1328 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X2 (M.op X3 (M.op X0 X1))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq382 X3 X1 (M.op X1 (M.op X0 X1)) X2
       have i₂ := eq1257 X1 X0
       grind)
    | exact superpose eq1257 eq382
    | exact resolve eq382 eq1257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq382 eq1257
  have eq1621 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = X0 ∨ (M.op X0 X0) = (σ (k X1 (τ X0))) ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq215 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq215
    | exact resolve eq215 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq1796 : ∀ X0 X1 : G, (M.op X0 X0) = (k (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 ∨ (σ (k X1 (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1621 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq1621
    | (have j0 := eq1621 X0 X1
       grind)
    | exact resolve eq1621 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1621
  have eq1811 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (k (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1796 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq1796
    | (have j0 := eq1796 X0 X1
       grind)
    | exact resolve eq1796 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796
  have eq2684 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ X2)) (M.op X0 X0)) = X0 ∨ (M.op (σ X2) X0) = (σ (k X2 (τ X0))) ∨ (M.op X0 (σ X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq175 X0 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq175
    | exact resolve eq175 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq2768 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (σ X2)) (M.op X0 X0)) = X0 ∨ (M.op (σ X2) X0) = (k (σ X2) X0) ∨ (M.op X0 (σ X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2684 X0 X1 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq2684
    | (have j0 := eq2684 X0 X1 X2
       grind)
    | exact resolve eq2684 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2684
  have eq9168 : ∀ X0 X1 : G, (M.op (M.op (k X0 X0) X1) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq563 (k X0 X0) X1 X0
       have i₂ := eq517 X0
       grind)
    | exact superpose eq517 eq563
    | (have j1 := eq517 X0
       grind)
    | exact resolve eq563 eq517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517 eq563
  have eq10565 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1328 x (k X0 X0) x X0
       have i₂ := eq710 X0 x (M.op x (k X0 X0))
       grind)
    | exact superpose eq710 eq1328
    | (have j1 := eq710 X0 x x
       grind)
    | exact resolve eq1328 eq710
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710 eq1328
  have eq10682 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (k X0 X0) X1
       have i₂ := eq10565 X0
       grind)
    | exact superpose eq10565 eq24
    | (have j1 := eq10565 X0
       grind)
    | exact resolve eq24 eq10565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11329 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq20 (σ X0)
       have i₂ := eq769 X0
       grind)
    | exact superpose eq769 eq20
    | (have j1 := eq769 X0
       grind)
    | exact resolve eq20 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq28053 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1811 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1811
  have eq37076 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (σ X1) X0) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1249 (σ x) (M.op X0 X0)
       have i₂ := eq2768 X0 (σ x) x
       grind)
    | exact superpose eq2768 eq1249
    | (have j1 := eq2768 X0 X1 X1
       grind)
    | exact resolve eq1249 eq2768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2768
  have eq37380 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (σ X1) X0) ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37076 X0 X1
       have i₂ := eq381 X0 X0
       grind)
    | exact superpose eq381 eq37076
    | (have j0 := eq37076 X0 X1
       grind)
    | exact resolve eq37076 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37076
  have eq37421 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq37380 X0 X1
       have j1 := eq28053 X1 X0
       grind)
    | (have r₁ := eq37380 X1 X0
       have r₂ := eq28053 X0 X1
       grind)
    | (have r₁ := eq37380 (σ X0) X0
       have r₂ := eq28053 X0 (σ X0)
       grind)
    | exact resolve eq37380 eq28053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28053 eq37380
  have eq37438 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq37421 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37421
    | exact resolve eq37421 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37473 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq37421 (σ X1) X0
       grind)
    | exact superpose eq37421 eq15
    | (have j1 := eq37421 (σ X1) X0
       grind)
    | exact resolve eq15 eq37421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37421
  have eq38174 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq37438 (τ X0) X1
       grind)
    | exact superpose eq37438 eq17
    | (have j1 := eq37438 (τ X0) X1
       grind)
    | exact resolve eq17 eq37438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq37438
  have eq45748 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq624 (k X0 X0) X1 (k X0 X0)
       have i₂ := eq10565 X0
       grind)
    | exact superpose eq10565 eq624
    | (have j0 := eq624 X0 X1 x
       have j1 := eq10565 X0
       grind)
    | exact resolve eq624 eq10565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624 eq10565
  have eq46060 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq45748 X0 X1
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq45748 X0 X1
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq45748 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45748
  have eq46268 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq639 (k X0 X0) X0
       have i₂ := eq46060 X0 (k X0 X0)
       grind)
    | exact superpose eq46060 eq639
    | (have j1 := eq46060 X0 x
       grind)
    | exact resolve eq639 eq46060
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46060
  have eq46737 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq20 (k X0 X0)
       have i₂ := eq46268 X0
       grind)
    | exact superpose eq46268 eq20
    | (have j1 := eq46268 X0
       grind)
    | exact resolve eq20 eq46268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46807 : ∀ X0 : G, (M.op X0 (k X0 X0)) = X0 ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq639 (k X0 X0) (k X0 X0)
       have i₂ := eq46268 X0
       grind)
    | exact superpose eq46268 eq639
    | (have j1 := eq46268 X0
       grind)
    | exact resolve eq639 eq46268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639 eq46268
  have eq56895 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38174 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq38174
    | exact resolve eq38174 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38174
  have eq57110 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq56895 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56895
    | (have j0 := eq56895 X0 X1
       grind)
    | exact resolve eq56895 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56895
  have eq59071 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9168 X0 (k (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq10682 (M.op X0 X0) (k X0 X0)
       grind)
    | exact superpose eq10682 eq9168
    | (have j0 := eq9168 X0 x
       have j1 := eq10682 X0 x
       grind)
    | exact resolve eq9168 eq10682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9168 eq10682
  have eq59447 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59071 X0
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq59071
    | (have j0 := eq59071 X0
       grind)
    | exact resolve eq59071 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59071
  have eq59448 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq59447 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59447
  have eq206211 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq37473 X1 X0
       grind)
    | exact superpose eq37473 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq37473 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq37473 X0 X1
       grind)
    | exact resolve eq12 eq37473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37473
  have eq206402 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq206211 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206211
  have eq206488 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq206402 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq206402
    | (have j0 := eq206402 X0 X1
       grind)
    | exact resolve eq206402 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206402
  have eq208082 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq206488 y x
       grind)
    | exact superpose eq206488 eq16
    | (have j1 := eq206488 y x
       grind)
    | exact resolve eq16 eq206488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206488
  have eq220618 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq208082
       have i₂ := eq57110 x y
       grind)
    | exact superpose eq57110 eq208082
    | (have j1 := eq57110 x y
       grind)
    | (have r₁ := eq208082
       have r₂ := eq57110 x y
       grind)
    | exact resolve eq208082 eq57110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57110 eq208082
  have eq220619 : (σ (M.op x y)) = (σ x) ∨ y = (M.op y x) := by grind
  clear eq220618
  have eq221126 : (M.op x y) = (τ (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq220619
       grind)
    | exact superpose eq220619 eq10
    | exact resolve eq10 eq220619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220619
  have eq221376 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq221126
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq221126
    | exact resolve eq221126 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221126
  have eq223950 : (M.op y x) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq381 x y
       have i₂ := eq221376
       grind)
    | exact superpose eq221376 eq381
    | exact resolve eq381 eq221376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230407 : y = (M.op x x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq221376
       have i₂ := eq223950
       grind)
    | exact superpose eq223950 eq221376
    | exact resolve eq221376 eq223950
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221376 eq223950
  have eq230602 : x = (M.op x y) ∨ y = (M.op x x) := by grind
  clear eq230407
  have eq231408 : (M.op x y) = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq381 y x
       have i₂ := eq230602
       grind)
    | exact superpose eq230602 eq381
    | exact resolve eq381 eq230602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq231423 : (M.op y x) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq722 y x
       have i₂ := eq230602
       grind)
    | exact superpose eq230602 eq722
    | exact resolve eq722 eq230602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722
  have eq245293 : y = (M.op y (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq20 y
       have i₂ := eq231408
       grind)
    | exact superpose eq231408 eq20
    | exact resolve eq20 eq231408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231408
  have eq256508 : y = (M.op y x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq245293
       have i₂ := eq230602
       grind)
    | exact superpose eq230602 eq245293
    | exact resolve eq245293 eq230602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230602 eq245293
  have eq256803 : y = (M.op y x) ∨ y = (M.op x x) := by grind
  clear eq256508
  have eq257957 : y = (M.op x x) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq231423
       have i₂ := eq256803
       grind)
    | exact superpose eq256803 eq231423
    | exact resolve eq231423 eq256803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231423 eq256803
  have eq258159 : y = (M.op x x) := by grind
  clear eq257957
  have eq260740 : x = (M.op x y) := by
    first
    | (have i₁ := eq20 x
       have i₂ := eq258159
       grind)
    | exact superpose eq258159 eq20
    | exact resolve eq20 eq258159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq260761 : ∀ X0 : G, (M.op X0 (M.op y X0)) = (M.op x (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq1249 x x
       have i₂ := eq258159
       grind)
    | exact superpose eq258159 eq1249
    | exact resolve eq1249 eq258159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249
  have eq260800 : x = (k y y) ∨ x = y := by
    first
    | (have i₁ := eq59448 x
       have i₂ := eq258159
       grind)
    | exact superpose eq258159 eq59448
    | exact resolve eq59448 eq258159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq260809 : x = (M.op y y) := by
    first
    | (have i₁ := eq24 x x
       have i₂ := eq258159
       grind)
    | exact superpose eq258159 eq24
    | exact resolve eq24 eq258159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq264282 : y = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq59448 y
       have i₂ := eq260809
       grind)
    | exact superpose eq260809 eq59448
    | exact resolve eq59448 eq260809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59448 eq260809
  have eq277410 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq11329 x
       have i₂ := eq264282
       grind)
    | exact superpose eq264282 eq11329
    | exact resolve eq11329 eq264282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11329 eq264282
  have eq305268 : (M.op x y) = (M.op (k y y) y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq260761 (k y y)
       have i₂ := eq46807 y
       grind)
    | exact superpose eq46807 eq260761
    | (have j1 := eq46807 y
       grind)
    | exact resolve eq260761 eq46807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46807 eq260761
  have eq306233 : x = (M.op (k y y) y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq305268
       have i₂ := eq260740
       grind)
    | exact superpose eq260740 eq305268
    | exact resolve eq305268 eq260740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305268
  have eq388472 : x = (k y y) ∨ y = (k y y) ∨ y = (k y y) := by
    first
    | (have i₁ := eq46737 y
       have i₂ := eq306233
       grind)
    | exact superpose eq306233 eq46737
    | (have j0 := eq46737 y
       grind)
    | exact resolve eq46737 eq306233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46737 eq306233
  have eq388695 : y = (k y y) ∨ x = (k y y) := by grind
  clear eq388472
  have eq390673 : x ≠ y ∨ x = (k y y) := by grind
  clear eq388695
  have eq390724 : x = (k y y) := by
    first
    | (have r₁ := eq390673
       have r₂ := eq260800
       grind)
    | exact resolve eq390673 eq260800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260800 eq390673
  have eq393817 : (σ x) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq192 y
       have i₂ := eq390724
       grind)
    | exact superpose eq390724 eq192
    | (have j0 := eq192 y
       grind)
    | exact resolve eq192 eq390724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq192 eq390724
  have eq1467446 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq277410
       grind)
    | exact superpose eq277410 eq16
    | exact resolve eq16 eq277410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277410
  have eq1468037 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1467446
       have i₂ := eq260740
       grind)
    | exact superpose eq260740 eq1467446
    | exact resolve eq1467446 eq260740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq260740 eq1467446
  have eq1468038 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1468037
  have eq1468920 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1468038
       grind)
    | exact superpose eq1468038 eq10
    | exact resolve eq10 eq1468038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468038
  have eq1469951 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1468920
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1468920
    | exact resolve eq1468920 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468920
  have eq1469952 : x = y := by grind
  clear eq1469951
  have eq1470803 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1469952
       grind)
    | exact superpose eq1469952 eq16
    | exact resolve eq16 eq1469952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1471097 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq393817
       have i₂ := eq1469952
       grind)
    | exact superpose eq1469952 eq393817
    | exact resolve eq393817 eq1469952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393817
  have eq1471105 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq1471097
  have eq1471156 : (σ y) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1470803
       have i₂ := eq258159
       grind)
    | exact superpose eq258159 eq1470803
    | exact resolve eq1470803 eq258159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258159 eq1470803
  have eq1471164 : (σ x) ≠ (σ y) := by
    first
    | (have i₁ := eq1471156
       have i₂ := eq1471105
       grind)
    | exact superpose eq1471105 eq1471156
    | exact resolve eq1471156 eq1471105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471105 eq1471156
  have eq1471168 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1471164
       have i₂ := eq1469952
       grind)
    | exact superpose eq1469952 eq1471164
    | exact resolve eq1471164 eq1469952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1469952 eq1471164
  have eq1471169 : False := by grind
  exact eq1471169

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyy_pyy_pyx_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq56 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (k x x)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op y y) := by
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
  have eq66 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq64
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq64
    | exact resolve eq64 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq67 : (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq66
    | exact resolve eq66 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq77 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : y = (M.op (M.op x y) (M.op y y)) := by
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
  have eq327 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq77 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq77
    | (have j0 := eq77 (σ X0)
       grind)
    | exact resolve eq77 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq331 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq44
       have i₂ := eq77 x
       grind)
    | exact superpose eq77 eq44
    | (have j1 := eq77 x
       grind)
    | exact resolve eq44 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X0) X2)) = (M.op X0 (M.op (M.op X1 (M.op (M.op X0 X0) X2)) (M.op X1 (M.op (M.op X0 X0) X2)))) := by
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
  have eq378 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op X2 X0) (M.op (M.op X1 X0) (M.op X1 X0))) := by
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
  have eq381 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X0) = (M.op (M.op X4 (M.op X2 (M.op X0 X3))) (M.op (M.op X1 X0) (M.op X1 X0))) := by
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
  clear eq49
  have eq3282 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq378 X0 X0 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq378
    | exact resolve eq378 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq3309 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq3282 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq3282
    | (have j0 := eq3282 y x
       grind)
    | exact resolve eq3282 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3311 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq27 eq3282
    | (have j0 := eq3282 (σ y) (σ x)
       grind)
    | exact resolve eq3282 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3282
  have eq3578 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq327 X0
       grind)
    | exact superpose eq327 eq50
    | (have j1 := eq327 X0
       grind)
    | exact resolve eq50 eq327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3590 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq327 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq3948 : ∀ X0 X1 X2 X3 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X2 (M.op X0 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq381 X0 X0 X2 X3 X1
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq381
    | exact resolve eq381 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381
  have eq6066 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq367 X0 X1 (M.op X0 X0)
       have i₂ := eq52 X0 X0
       grind)
    | exact superpose eq52 eq367
    | exact resolve eq367 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq18278 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3948 X0 (M.op X0 X1) (M.op X0 X1) X1
       have i₂ := eq50 (M.op X0 X1)
       grind)
    | exact superpose eq50 eq3948
    | exact resolve eq3948 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq3948
  have eq18907 : ∀ X0 X1 X2 : G, (M.op (M.op X2 (M.op X0 X1)) (M.op X1 X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq6066 X1 X0
       grind)
    | exact superpose eq6066 eq14
    | exact resolve eq14 eq6066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6066
  have eq26577 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3590 x
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq3590
    | (have j0 := eq3590 x
       grind)
    | exact resolve eq3590 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq26582 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26577
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26577
    | exact resolve eq26577 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26577
  have eq26589 : (σ x) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26582
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq26582
    | exact resolve eq26582 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26582
  have eq33372 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq52 y y
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq52
    | exact resolve eq52 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq33413 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq33372
       have i₂ := eq52 x x
       grind)
    | exact superpose eq52 eq33372
    | exact resolve eq33372 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33372
  have eq33430 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq33413 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq33413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq33430
    | exact resolve eq33430 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33430
  have eq33442 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq33431
       have r₂ := eq28
       grind)
    | exact resolve eq33431 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33431
  have eq33508 : ∀ X0 : G, (σ y) = (M.op (M.op X0 (M.op (σ x) (σ x))) (M.op (σ x) (σ x))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    intro X0
    first
    | exact superpose eq33442 eq18907
    | exact resolve eq18907 eq33442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18907 eq33442
  have eq33519 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq33508 x
       have i₂ := eq14 sF2 x sF2
       grind)
    | exact superpose eq14 eq33508
    | exact resolve eq33508 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33508
  have eq33600 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | exact superpose eq33519 eq18278
    | exact resolve eq18278 eq33519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33519
  have eq33615 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq33600
    | exact resolve eq33600 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33600
  have eq34510 : y = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq52 y y
       have i₂ := eq33615
       grind)
    | exact superpose eq33615 eq52
    | exact resolve eq52 eq33615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq34529 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18278 y y
       have i₂ := eq33615
       grind)
    | exact superpose eq33615 eq18278
    | exact resolve eq18278 eq33615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33615
  have eq34544 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq34529
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq34529
    | exact resolve eq34529 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34529
  have eq34570 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq34544 eq28
    | exact resolve eq28 eq34544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34579 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq34544 eq3311
    | exact resolve eq3311 eq34544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3311
  have eq34648 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq34579
    | exact resolve eq34579 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34579
  have eq34757 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq331
       have i₂ := eq34510
       grind)
    | exact superpose eq34510 eq331
    | exact resolve eq331 eq34510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34510
  have eq34813 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq34757
  have eq34820 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq34813
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq34813
    | exact resolve eq34813 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34813
  have eq35045 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq34648
  have eq35174 : (τ (σ y)) = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34820 eq56
    | exact resolve eq56 eq34820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq34820
  have eq35195 : y = (k x x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq35174
    | exact resolve eq35174 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35174
  have eq35227 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq34544 eq35045
    | exact resolve eq35045 eq34544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34544 eq35045
  have eq35230 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq35227
  have eq35376 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq35230 eq33413
    | exact resolve eq33413 eq35230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33413 eq35230
  have eq35378 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq35376
  have eq35381 : x = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq35378
       have r₂ := eq34570
       grind)
    | exact resolve eq35378 eq34570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34570 eq35378
  have eq35544 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18278 y y
       have i₂ := eq35381
       grind)
    | exact superpose eq35381 eq18278
    | exact resolve eq18278 eq35381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18278 eq35381
  have eq35559 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq35544
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq35544
    | exact resolve eq35544 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35544
  have eq35560 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq35559
  have eq35589 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq35560 eq30
    | exact resolve eq30 eq35560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35560
  have eq35787 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq35589
    | exact resolve eq35589 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq35589
  have eq35788 : x = (M.op x y) ∨ x = y := by grind
  clear eq35787
  have eq35789 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq35788 eq21
    | exact resolve eq21 eq35788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35835 : y = (M.op x (M.op y y)) ∨ x = y := by
    first
    | exact superpose eq35788 eq225
    | exact resolve eq225 eq35788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq35857 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq35788 eq3309
    | exact resolve eq3309 eq35788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3309
  have eq35934 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq35857
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq35857
    | exact resolve eq35857 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35857
  have eq35995 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq35789
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq35789
    | exact resolve eq35789 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35789
  have eq37549 : y = (M.op x (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq35835
       have i₂ := eq35934
       grind)
    | exact superpose eq35934 eq35835
    | exact resolve eq35835 eq35934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35835 eq35934
  have eq37607 : y = (M.op x (M.op x y)) ∨ x = y := by grind
  clear eq37549
  have eq37621 : y = (M.op x x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq35788 eq37607
    | exact resolve eq37607 eq35788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37607
  have eq37667 : y = (M.op x x) ∨ x = y := by grind
  clear eq37621
  have eq37674 : (σ y) = (k (σ x) (σ x)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq331
       have i₂ := eq37667
       grind)
    | exact superpose eq37667 eq331
    | exact resolve eq331 eq37667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37667
  have eq37733 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by grind
  clear eq37674
  have eq37739 : (σ y) = (k (σ x) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq37733
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq37733
    | exact resolve eq37733 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37733
  have eq38028 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq35995 eq37739
    | exact resolve eq37739 eq35995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38041 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y := by
    first
    | exact superpose eq37739 eq26589
    | exact resolve eq26589 eq37739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26589 eq37739
  have eq38047 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq38028
  have eq90186 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3578 x
       have i₂ := eq35195
       grind)
    | exact superpose eq35195 eq3578
    | (have j0 := eq3578 x
       grind)
    | exact resolve eq3578 eq35195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3578 eq35195
  have eq90279 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq90186
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq90186
    | exact resolve eq90186 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90186
  have eq90309 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq90279
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq90279
    | exact resolve eq90279 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90279
  have eq90328 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq90309
    | exact resolve eq90309 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90309
  have eq90329 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq90328
  have eq90338 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq90329
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq90329
    | exact resolve eq90329 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90329
  have eq90342 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have r₁ := eq90338
       have r₂ := eq38041
       grind)
    | exact resolve eq90338 eq38041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38041 eq90338
  have eq90344 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq35995 eq90342
    | exact resolve eq90342 eq35995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35995 eq90342
  have eq90412 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq90344
  have eq90427 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have r₁ := eq90412
       have r₂ := eq28
       grind)
    | exact resolve eq90412 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90412
  have eq90438 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq90427
  have eq90514 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq90438 eq38047
    | exact resolve eq38047 eq90438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38047 eq90438
  have eq90527 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq90514
  have eq90716 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq90527 eq30
    | exact resolve eq30 eq90527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq90527
  have eq91059 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq90716
    | exact resolve eq90716 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq90716
  have eq91260 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq91059 eq35788
    | exact resolve eq35788 eq91059
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35788 eq91059
  have eq91442 : x = y := by grind
  clear eq91260
  have eq91648 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq91442
       grind)
    | exact superpose eq91442 eq19
    | exact resolve eq19 eq91442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq91649 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq91442
       grind)
    | exact superpose eq91442 eq25
    | exact resolve eq25 eq91442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq91442
  have eq91965 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq91649
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq91649
    | exact resolve eq91649 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91649
  have eq91969 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq91965 eq27
    | exact resolve eq27 eq91965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq91965
  have eq92247 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq331
       have i₂ := eq91648
       grind)
    | exact superpose eq91648 eq331
    | exact resolve eq331 eq91648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq331
  have eq92289 : (M.op x y) = (k (M.op x y) x) := by grind
  clear eq91648
  have eq92353 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq92247
    | exact resolve eq92247 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92247
  have eq92391 : (M.op (σ x) (σ y)) = (k (M.op (σ x) (σ y)) (σ x)) := by grind
  have eq104875 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq92353 eq77
    | (have j0 := eq77 (σ x)
       grind)
    | exact resolve eq77 eq92353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq104876 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq91969 eq104875
    | exact resolve eq104875 eq91969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104875
  have eq104890 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq104876
       have r₂ := eq28
       grind)
    | exact resolve eq104876 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104876
  have eq104897 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq91969 eq104890
    | exact resolve eq104890 eq91969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104890
  have eq105906 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104897 eq28
    | exact resolve eq28 eq104897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105989 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq104897 eq92391
    | exact resolve eq92391 eq104897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92391 eq104897
  have eq107175 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105989 eq92353
    | exact resolve eq92353 eq105989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92353 eq105989
  have eq107191 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq107175
  have eq107200 : x = (M.op x y) := by
    first
    | (have r₁ := eq107191
       have r₂ := eq105906
       grind)
    | exact resolve eq107191 eq105906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105906 eq107191
  have eq107222 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq107200 eq21
    | exact resolve eq21 eq107200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq107495 : x = (k x x) := by
    first
    | exact superpose eq107200 eq92289
    | exact resolve eq92289 eq107200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92289 eq107200
  have eq107689 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq107222
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq107222
    | exact resolve eq107222 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107222
  have eq108258 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq3590 x
       have i₂ := eq107495
       grind)
    | exact superpose eq107495 eq3590
    | (have j0 := eq3590 x
       grind)
    | exact resolve eq3590 eq107495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3590 eq107495
  have eq108262 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq108258
  have eq108274 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq108262
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq108262
    | exact resolve eq108262 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq108262
  have eq108292 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq91969 eq108274
    | exact resolve eq108274 eq91969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91969 eq108274
  have eq108308 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq107689 eq108292
    | exact resolve eq108292 eq107689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107689 eq108292
  have eq108323 : False := by grind
  exact eq108323

/-- `Equation1904`: `x = (y ◇ (x ◇ z)) ◇ (x ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_pyy_pxy_Equation1904 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1904 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1904.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = (k X0 X1) ∨ (M.op X0 X0) ≠ X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq21 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 X3)) = (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X0 X3)) (M.op X2 (M.op X0 X3)))) := by
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
  have eq22 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = X0 := by
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
  have eq24 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op X0 X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op (M.op X0 X0) X2)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) X1 X2
       have i₂ := eq24 X0 X0
       grind)
    | exact superpose eq24 eq9
    | exact resolve eq9 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (k X0 (M.op X0 X0)) = (M.op X0 (M.op X0 X0)) := by
    intro X0
    grind
  have eq34 : ∀ X0 : G, (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq33
    | exact resolve eq33 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq43 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq75 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X2 X0) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 X2 (M.op X0 X1) X1
       have i₂ := eq24 (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq24 eq21
    | exact resolve eq21 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) (M.op (M.op X4 X1) (M.op X4 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X4 X1) X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq21 X1 X4 X0 X2
       grind)
    | exact superpose eq21 eq9
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    first
    | (have i₁ := eq75 X0 (M.op (σ X0) (σ X0))
       have i₂ := eq34 (σ X0)
       grind)
    | exact superpose eq34 eq75
    | exact resolve eq75 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq127 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq118 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq118
    | exact resolve eq118 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq147 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq43 x y
       grind)
    | exact superpose eq43 eq16
    | (have j1 := eq43 x y
       grind)
    | exact resolve eq16 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq156 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq24
    | (have j1 := eq43 X0 X0
       grind)
    | exact resolve eq24 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq43 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq162 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq161 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq167 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (M.op X1 (σ X0)) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq156 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq156
  have eq169 : ∀ X0 : G, (k (σ X0) (σ (k X0 X0))) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq154 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154
  have eq174 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ (k X0 X0)) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq169 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq169
    | (have j0 := eq169 X0
       grind)
    | exact resolve eq169 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq169
  have eq261 : ∀ X0 X1 X2 X3 : G, (M.op X1 X1) = (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq32 X1 X3 (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq21 X1 X1 X0 X2
       grind)
    | exact superpose eq21 eq32
    | exact resolve eq32 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq361 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq261 (M.op X0 X1) X0 X1 (M.op X0 X1)
       have i₂ := eq22 (M.op X0 X1)
       grind)
    | exact superpose eq22 eq261
    | exact resolve eq261 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq415 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X2)) (M.op X1 (M.op X0 X2))) = (M.op X0 (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq361 (M.op X1 (M.op X0 X2)) (M.op X0 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq361
    | exact resolve eq361 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq361 (M.op X1 X0) (M.op X0 X0)
       have i₂ := eq24 X0 X1
       grind)
    | exact superpose eq24 eq361
    | exact resolve eq361 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X1) (M.op X3 X1)) = (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq361 (M.op X3 X1) (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2)))
       have i₂ := eq21 X1 X3 X0 X2
       grind)
    | exact superpose eq21 eq361
    | exact resolve eq361 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X0 X2))) = (M.op (M.op X0 X2) (M.op X1 (M.op X0 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq415 X0 X1 X2
       have i₂ := eq416 (M.op X0 X2) X1
       grind)
    | exact superpose eq416 eq415
    | exact resolve eq415 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq601 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq162 (τ X0)
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq162
    | (have j0 := eq162 (τ X0)
       grind)
    | exact resolve eq162 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162
  have eq603 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq601 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq601
    | (have j0 := eq601 X0
       grind)
    | exact resolve eq601 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq606 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq603 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq603
    | (have j0 := eq603 X0
       grind)
    | exact resolve eq603 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq603
  have eq652 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op X1 X0)
       have i₂ := eq416 X0 X1
       grind)
    | exact superpose eq416 eq22
    | exact resolve eq22 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq652 X0 X1
       have i₂ := eq439 X1 X0 X0
       grind)
    | exact superpose eq439 eq652
    | exact resolve eq652 eq439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439 eq652
  have eq807 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op (M.op X2 X0) (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq113 X1 X0 X1 X0 X2
       have i₂ := eq661 X1 X0
       grind)
    | exact superpose eq661 eq113
    | exact resolve eq113 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq870 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X0 X1) (M.op X0 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq807 X0 X1 X2
       have i₂ := eq416 X0 X2
       grind)
    | exact superpose eq416 eq807
    | exact resolve eq807 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq1201 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 X0 X2 X1 X1
       have i₂ := eq870 X1 (M.op X0 X1) X0
       grind)
    | exact superpose eq870 eq21
    | exact resolve eq21 eq870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq870
  have eq1721 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X1 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq661 X2 X1
       have i₂ := eq1201 X1 X2 X0
       grind)
    | (have i₁ := eq661 (M.op X2 X0) X0
       have i₂ := eq1201 X0 (M.op X2 X0) X2
       grind)
    | exact superpose eq1201 eq661
    | exact resolve eq661 eq1201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq2824 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq147
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq147
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | exact resolve eq147 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147
  have eq2825 : y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq2824
  have eq3963 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq174 x
       have i₂ := eq14 x x
       grind)
    | exact superpose eq14 eq174
    | (have j0 := eq174 X0
       have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq174 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq4028 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq3963 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3963
  have eq4033 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4028 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq4028
    | (have j0 := eq4028 X0
       grind)
    | exact resolve eq4028 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4028
  have eq4034 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq4033 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4033
  have eq10636 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op X1 X0) (σ (k (τ X0) (τ X0)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq167 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq167
    | exact resolve eq167 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq167
  have eq10767 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k (σ (τ X0)) X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10636 X0 X1
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq10636
    | (have j0 := eq10636 X0 X1
       grind)
    | exact resolve eq10636 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10636
  have eq10773 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10767 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10767
    | (have j0 := eq10767 X0 X1
       grind)
    | exact resolve eq10767 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10767
  have eq10839 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq361 (k X0 X0) X0
       have i₂ := eq10773 X0 (k X0 X0)
       grind)
    | exact superpose eq10773 eq361
    | (have j1 := eq10773 X0 x
       grind)
    | exact resolve eq361 eq10773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10773
  have eq11012 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq24 (k X0 X0) (k X0 X0)
       have i₂ := eq10839 X0
       grind)
    | exact superpose eq10839 eq24
    | (have j1 := eq10839 X0
       grind)
    | exact resolve eq24 eq10839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10839
  have eq11353 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq11012 (σ X0)
       grind)
    | exact superpose eq11012 eq15
    | (have j1 := eq11012 (σ X0)
       grind)
    | exact resolve eq15 eq11012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11012
  have eq38719 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 (M.op X1 X2)) (M.op X3 X1)) = (M.op (M.op X4 X3) (M.op X3 X1)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq109 X3 X1 X4
       have i₂ := eq418 X0 X1 X2 X3
       grind)
    | exact superpose eq418 eq109
    | exact resolve eq109 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq418
  have eq40316 : ∀ X0 : G, (k X0 (τ (σ X0))) = X0 ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq127 X0
       have i₂ := eq4034 X0
       grind)
    | exact superpose eq4034 eq127
    | (have j1 := eq4034 X0
       grind)
    | exact resolve eq127 eq4034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4034
  have eq40498 : ∀ X0 : G, (k X0 X0) = X0 ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq40316 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq40316
    | (have j0 := eq40316 X0
       grind)
    | exact resolve eq40316 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40316
  have eq40516 : ∀ X0 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq40498 X0
       have j1 := eq606 X0
       grind)
    | (have r₁ := eq40498 X0
       have r₂ := eq606 X0
       grind)
    | exact resolve eq40498 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606 eq40498
  have eq41114 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq24 x x
       have i₂ := eq2825
       grind)
    | exact superpose eq2825 eq24
    | exact resolve eq24 eq2825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2825
  have eq41204 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq41114
  have eq54746 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X1)) = (M.op (M.op X3 X2) (M.op X2 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq38719 X0 X1 (M.op X0 X1) X2 X3
       have i₂ := eq661 X1 X0
       grind)
    | exact superpose eq661 eq38719
    | exact resolve eq38719 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661 eq38719
  have eq174004 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  clear eq11353
  have eq174295 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq174004 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq174004
    | (have j0 := eq174004 X0
       grind)
    | exact resolve eq174004 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174004
  have eq174296 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq174295 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174295
  have eq174377 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq174296 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq174296
    | exact resolve eq174296 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq174476 : ∀ X0 : G, (k X0 (τ (σ (k X0 X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq127 X0
       have i₂ := eq174296 X0
       grind)
    | exact superpose eq174296 eq127
    | exact resolve eq127 eq174296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq174541 : ∀ X0 : G, (σ X0) = (k (σ X0) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq34 (σ X0)
       have i₂ := eq174296 X0
       grind)
    | exact superpose eq174296 eq34
    | exact resolve eq34 eq174296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq174893 : ∀ X0 : G, (σ X0) = (σ (k X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq174541 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq174541
    | exact resolve eq174541 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174541
  have eq174918 : ∀ X0 : G, (k X0 (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq174476 X0
       have i₂ := eq10 (k X0 X0)
       grind)
    | exact superpose eq10 eq174476
    | exact resolve eq174476 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174476
  have eq174955 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq174377 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq174377
    | exact resolve eq174377 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq174377
  have eq175040 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq174955 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq174955
    | exact resolve eq174955 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174955
  have eq178579 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k (k X0 (k X0 X0)) (k X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq174296 (k X0 (k X0 X0))
       have i₂ := eq174893 X0
       grind)
    | exact superpose eq174893 eq174296
    | exact resolve eq174296 eq174893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174893
  have eq178587 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op (k X0 (k X0 X0)) (k X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq178579 X0
       have i₂ := eq175040 (k X0 (k X0 X0))
       grind)
    | exact superpose eq175040 eq178579
    | exact resolve eq178579 eq175040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178579
  have eq178732 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq178587 X0
       have i₂ := eq174918 X0
       grind)
    | exact superpose eq174918 eq178587
    | exact resolve eq178587 eq174918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174918 eq178587
  have eq184047 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq178732 X0
       grind)
    | exact superpose eq178732 eq24
    | exact resolve eq24 eq178732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq184138 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq361 (σ X0) (σ X0)
       have i₂ := eq178732 X0
       grind)
    | exact superpose eq178732 eq361
    | exact resolve eq361 eq178732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184194 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (M.op X1 (σ X0)) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq1721 X0 (σ X0) (σ X0)
       have i₂ := eq178732 X0
       grind)
    | exact superpose eq178732 eq1721
    | exact resolve eq1721 eq178732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1721
  have eq197806 : ∀ X0 X1 X2 X3 : G, (σ (M.op X1 X2)) = (M.op (M.op X3 (σ (M.op X1 X2))) (σ (M.op (M.op X0 X1) (M.op X1 X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq184047 (M.op X1 X2) X3
       have i₂ := eq54746 X1 X2 X1 X0
       grind)
    | (have i₁ := eq184047 (M.op X1 X1) X1
       have i₂ := eq54746 X0 X1 X1 X1
       grind)
    | exact superpose eq54746 eq184047
    | exact resolve eq184047 eq54746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184047
  have eq314503 : ∀ X0 X1 X2 X3 : G, (σ (M.op (M.op X0 X1) (M.op X1 X2))) = (M.op (σ (M.op X1 X2)) (M.op (M.op X3 (σ (M.op X1 X2))) (σ (M.op (M.op X0 X1) (M.op X1 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq184194 (M.op X2 X1) X1
       have i₂ := eq54746 X2 X1 X2 X3
       grind)
    | (have i₁ := eq184194 (M.op X1 X1) X1
       have i₂ := eq54746 X0 X1 X1 X1
       grind)
    | exact superpose eq54746 eq184194
    | exact resolve eq184194 eq54746
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54746 eq184194
  have eq315141 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) (M.op X1 X2))) = (M.op (σ (M.op X1 X2)) (σ (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq314503 X0 X1 X2 x
       have i₂ := eq197806 X0 X1 X2 x
       grind)
    | exact superpose eq197806 eq314503
    | exact resolve eq314503 eq197806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197806 eq314503
  have eq315453 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) (M.op X1 X2))) = (σ (k (M.op X1 X2) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq315141 X0 X1 X2
       have i₂ := eq174296 (M.op X1 X2)
       grind)
    | exact superpose eq174296 eq315141
    | exact resolve eq315141 eq174296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315141
  have eq315629 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X1 X2) (M.op X1 X2))) = (σ (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq315453 X0 X1 X2
       have i₂ := eq175040 (M.op X1 X2)
       grind)
    | exact superpose eq175040 eq315453
    | exact resolve eq315453 eq175040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315453
  have eq315742 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X1) (M.op X1 X2))) = (σ (M.op X2 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq315629 X0 X1 X2
       have i₂ := eq416 X2 X1
       grind)
    | exact superpose eq416 eq315629
    | exact resolve eq315629 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq315629
  have eq1358184 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq40516 y
       have i₂ := eq41204
       grind)
    | exact superpose eq41204 eq40516
    | exact resolve eq40516 eq41204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40516 eq41204
  have eq1358579 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1358184
  have eq1358962 : (σ y) = (σ (k x x)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1358579
       have i₂ := eq174296 x
       grind)
    | exact superpose eq174296 eq1358579
    | exact resolve eq1358579 eq174296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358579
  have eq1359436 : (σ y) = (σ (M.op x x)) ∨ x = y ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1358962
       have i₂ := eq175040 x
       grind)
    | exact superpose eq175040 eq1358962
    | exact resolve eq1358962 eq175040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1358962
  have eq1359902 : (σ x) = (σ (k y y)) ∨ (σ y) = (σ (M.op x x)) ∨ x = y := by
    first
    | (have i₁ := eq1359436
       have i₂ := eq174296 y
       grind)
    | exact superpose eq174296 eq1359436
    | exact resolve eq1359436 eq174296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359436
  have eq1360367 : x = y ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1359902
       have i₂ := eq175040 y
       grind)
    | exact superpose eq175040 eq1359902
    | exact resolve eq1359902 eq175040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359902
  have eq1360624 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1360367
       grind)
    | exact superpose eq1360367 eq16
    | exact resolve eq16 eq1360367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360367
  have eq1360627 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq1360624
       have r₂ := eq178732 x
       grind)
    | exact resolve eq1360624 eq178732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360624
  have eq1361133 : (M.op (σ y) (σ y)) = (σ (M.op (M.op x x) (M.op x x))) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq178732 (M.op x x)
       have i₂ := eq1360627
       grind)
    | exact superpose eq1360627 eq178732
    | exact resolve eq178732 eq1360627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178732 eq1360627
  have eq1361200 : (M.op (σ y) (σ y)) = (σ (M.op x (M.op x x))) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1361133
       have i₂ := eq315742 x x x
       grind)
    | exact superpose eq315742 eq1361133
    | exact resolve eq1361133 eq315742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315742 eq1361133
  have eq1361674 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1361200
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq1361200
    | exact resolve eq1361200 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1361200
  have eq1362085 : (σ x) = (σ (k y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1361674
       have i₂ := eq174296 y
       grind)
    | exact superpose eq174296 eq1361674
    | exact resolve eq1361674 eq174296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174296 eq1361674
  have eq1362310 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq1362085
       have i₂ := eq175040 y
       grind)
    | exact superpose eq175040 eq1362085
    | exact resolve eq1362085 eq175040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175040 eq1362085
  have eq1362311 : (σ x) = (σ (M.op y y)) := by grind
  clear eq1362310
  have eq1367020 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq184138 y
       have i₂ := eq1362311
       grind)
    | exact superpose eq1362311 eq184138
    | exact resolve eq184138 eq1362311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184138
  have eq1367045 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq1362311
       grind)
    | exact superpose eq1362311 eq10
    | exact resolve eq10 eq1362311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362311
  have eq1367960 : x = (M.op y y) := by
    first
    | (have i₁ := eq1367045
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1367045
    | exact resolve eq1367045 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367045
  have eq1369647 : x = (M.op x y) := by
    first
    | (have i₁ := eq361 y y
       have i₂ := eq1367960
       grind)
    | exact superpose eq1367960 eq361
    | exact resolve eq361 eq1367960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361 eq1367960
  have eq1401139 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1367020
       grind)
    | exact superpose eq1367020 eq16
    | exact resolve eq16 eq1367020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1367020
  have eq1401749 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1401139
       have i₂ := eq1369647
       grind)
    | exact superpose eq1369647 eq1401139
    | exact resolve eq1401139 eq1369647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369647 eq1401139
  have eq1401750 : False := by grind
  exact eq1401750
