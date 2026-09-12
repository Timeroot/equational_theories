import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,Y) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_x_x_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq46 : (σ (k x (M.op x y))) = (k (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq36
    | (have j0 := eq36 (M.op x y)
       grind)
    | exact resolve eq36 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq51 : y ≠ (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | exact resolve eq13 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq60 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 x y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (k x (M.op x y)) = (τ (k (σ x) (σ (M.op x y)))) := by
    first
    | exact superpose eq46 eq16
    | exact resolve eq16 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
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
  have eq100 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq92
    | exact resolve eq92 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq102 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq128 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq151 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq128 eq16
    | exact resolve eq16 eq128
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128
  have eq210 : y = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | (have i₁ := eq57 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq57
    | (have j0 := eq57 y
       grind)
    | exact resolve eq57 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq392 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq59 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq400 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq392 X0
       grind)
    | exact superpose eq392 eq14
    | exact resolve eq14 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op X0 X0) X0
       have i₂ := eq392 X0
       grind)
    | exact superpose eq392 eq13
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq392 X0
       grind)
    | exact resolve eq13 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq402 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402
  have eq614 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) X3) (σ X1)) X3) = X3 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 (σ X1) (σ X0) X2 X3
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq62
    | (have j1 := eq84 X0 X1
       grind)
    | exact resolve eq62 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq615 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op (σ X0) X2) (σ (k X0 X1))) X3) X2) X3) = X3 ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 X2 (σ X0) (σ X1) X3
       have i₂ := eq84 X0 X1
       grind)
    | exact superpose eq84 eq62
    | (have j1 := eq84 X0 X1
       grind)
    | exact resolve eq62 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq622 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq84 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq624 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq622 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq959 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq400 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq400
    | exact resolve eq400 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq962 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq60 eq400
    | exact resolve eq400 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60 eq400
  have eq983 : (M.op x y) ≠ (M.op x y) ∨ x = (k x (M.op x y)) := by
    first
    | exact superpose eq962 eq13
    | (have j0 := eq13 x (M.op x y)
       grind)
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq962
       grind)
    | exact resolve eq13 eq962
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq962
  have eq993 : x = (k x (M.op x y)) := by grind
  clear eq983
  have eq4251 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq624 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq624
    | (have j0 := eq624 (τ X0)
       grind)
    | exact resolve eq624 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq624
  have eq4259 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4251 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4251
    | (have j0 := eq4251 X0
       grind)
    | exact resolve eq4251 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4251
  have eq4265 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4259 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4259
    | (have j0 := eq4259 X0
       grind)
    | exact resolve eq4259 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4259
  have eq8284 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq103 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8285 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq8284
    | exact resolve eq8284 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8284
  have eq8296 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq8285
       have r₂ := eq28
       grind)
    | exact resolve eq8285 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8285
  have eq8299 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq8296
    | exact resolve eq8296 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8296
  have eq8419 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq8299 eq392
    | exact resolve eq392 eq8299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8299
  have eq8444 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq8419
    | exact resolve eq8419 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8419
  have eq8445 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq8444
  have eq8449 : x = (k x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq403 y
       have i₂ := eq8445
       grind)
    | exact superpose eq8445 eq403
    | exact resolve eq403 eq8445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403 eq8445
  have eq8477 : x = (k x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq8449
       have r₂ := eq51
       grind)
    | exact resolve eq8449 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq8449
  have eq8945 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq8477
       grind)
    | exact superpose eq8477 eq45
    | exact resolve eq45 eq8477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8477
  have eq8960 : (σ x) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8945
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8945
    | exact resolve eq8945 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8945
  have eq8964 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq8960
       have r₂ := eq52
       grind)
    | exact resolve eq8960 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq8960
  have eq8966 : x = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq103 eq8964
    | exact resolve eq8964 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq9547 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq392 y
       have i₂ := eq8966
       grind)
    | exact superpose eq8966 eq392
    | exact resolve eq392 eq8966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8966
  have eq9571 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq9547
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq9547
    | exact resolve eq9547 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9547
  have eq9572 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq9571
  have eq9576 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9572 eq29
    | exact resolve eq29 eq9572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq9587 : (k x (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9572 eq68
    | exact resolve eq68 eq9572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq9572
  have eq9689 : (k x (M.op x y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq151 eq9587
    | exact resolve eq9587 eq151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151 eq9587
  have eq9696 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq9576
    | exact resolve eq9576 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq9576
  have eq9703 : x = (k (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq993 eq9689
    | exact resolve eq9689 eq993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq993 eq9689
  have eq9707 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9696 eq21
    | exact resolve eq21 eq9696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9837 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq9707
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq9707
    | exact resolve eq9707 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9707
  have eq10472 : x ≠ (M.op x y) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq9703 eq4265
    | (have j0 := eq4265 (M.op x y)
       grind)
    | exact resolve eq4265 eq9703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4265 eq9703
  have eq10479 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq10472
       have r₂ := eq9696
       grind)
    | exact resolve eq10472 eq9696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9696 eq10472
  have eq11935 : y = (M.op (M.op x y) y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq10479 eq210
    | exact resolve eq210 eq10479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq10479
  have eq18780 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) X0) (k (σ x) (σ y))) X1) X0) X1) = X1 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq615 x y X0 X1
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq615
    | (have j0 := eq615 x y x x
       grind)
    | exact resolve eq615 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq18912 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq8964 eq18780
    | exact resolve eq18780 eq8964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18780
  have eq19037 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq18912 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq18912
    | (have j0 := eq18912 X0 X1
       grind)
    | exact resolve eq18912 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18912
  have eq19159 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq19037 X0 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19037
    | (have j0 := eq19037 X0 X1
       grind)
    | exact resolve eq19037 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19037
  have eq19266 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq19159 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19159
    | (have j0 := eq19159 X0 X1
       grind)
    | exact resolve eq19159 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19159
  have eq19367 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19266 X0 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19266
    | (have j0 := eq19266 X0 X1
       grind)
    | exact resolve eq19266 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19266
  have eq19437 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19367 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq19367
    | (have j0 := eq19367 X0 X1
       grind)
    | exact resolve eq19367 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19367
  have eq19459 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq19437
    | (have j0 := eq19437 X0 X1
       grind)
    | exact resolve eq19437 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19437
  have eq19737 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (k (σ x) (σ y)) (M.op (σ x) X0)) X1) (σ y)) X1) = X1 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq614 x y X0 X1
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq614
    | (have j0 := eq614 x y x x
       grind)
    | exact resolve eq614 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq614
  have eq20061 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (k (σ x) (σ y)) (M.op (σ x) X0)) X1) (σ y)) X1) = X1 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq19737 X0 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq19737
    | (have j0 := eq19737 X0 X1
       grind)
    | exact resolve eq19737 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19737
  have eq20239 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (k (σ x) (σ y)) (M.op (σ x) X0)) X1) (σ y)) X1) = X1 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq20061 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20061
    | (have j0 := eq20061 X0 X1
       grind)
    | exact resolve eq20061 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20061
  have eq20366 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (M.op (σ x) X0)) X1) (σ y)) X1) = X1 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq8964 eq20239
    | exact resolve eq20239 eq8964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8964 eq20239
  have eq20491 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) X1) = X1 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq20366 X1 X1
       have i₂ := eq959 sF2 X1
       grind)
    | exact superpose eq959 eq20366
    | exact resolve eq20366 eq959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq959 eq20366
  have eq20596 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq20491 X0 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20491
    | (have j0 := eq20491 X0 X1
       grind)
    | exact resolve eq20491 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20491
  have eq20692 : ∀ X0 X1 : G, (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq20596 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20596
    | (have j0 := eq20596 X0 X1
       grind)
    | exact resolve eq20596 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20596
  have eq20764 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20692 X0 X1
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq20692
    | (have j0 := eq20692 X0 X1
       grind)
    | exact resolve eq20692 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20692
  have eq20798 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20764 X0 X1
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq20764
    | (have j0 := eq20764 X0 X1
       grind)
    | exact resolve eq20764 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20764
  have eq20808 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) X1) = X1 ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq27 eq20798
    | (have j0 := eq20798 X0 X1
       grind)
    | exact resolve eq20798 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20798
  have eq28371 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20808 eq19459
    | exact resolve eq19459 eq20808
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19459 eq20808
  have eq28425 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28371
  have eq28428 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq28425
    | exact resolve eq28425 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28425
  have eq28429 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28428
  have eq28435 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28429 eq392
    | exact resolve eq392 eq28429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392 eq28429
  have eq28487 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq28435
    | exact resolve eq28435 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq28435
  have eq28488 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28487
  have eq28492 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq28488 eq28
    | exact resolve eq28 eq28488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq28488
  have eq28540 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq9837 eq28492
    | (have r₁ := eq28492
       have r₂ := eq9837
       grind)
    | exact resolve eq28492 eq9837
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9837
  have eq28541 : x = (M.op x y) := by grind
  clear eq28540
  have eq28543 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq28541 eq21
    | exact resolve eq21 eq28541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq28635 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq28541 eq11935
    | exact resolve eq11935 eq28541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11935
  have eq28644 : y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq28635
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq28635
    | exact resolve eq28635 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq28635
  have eq28707 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq28543
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28543
    | exact resolve eq28543 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28543
  have eq28708 : x = y ∨ x = y := by
    first
    | exact superpose eq28541 eq28644
    | exact resolve eq28644 eq28541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28541 eq28644
  have eq28709 : x = y := by grind
  clear eq28708
  have eq29358 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq28709
       grind)
    | exact superpose eq28709 eq25
    | exact resolve eq25 eq28709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq28709
  have eq29519 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq29358
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq29358
    | exact resolve eq29358 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq29358
  have eq29583 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq28707 eq29519
    | exact resolve eq29519 eq28707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28707 eq29519
  have eq29613 : False := by grind
  exact eq29613

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_y_pyx_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq78 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq78 y x
       grind)
    | exact superpose eq78 eq75
    | (have j1 := eq78 x x
       grind)
    | exact resolve eq75 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
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
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq109
    | exact resolve eq109 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq110 eq78
    | (have j0 := eq78 x (σ x)
       grind)
    | exact resolve eq78 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq729 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq728
    | exact resolve eq728 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq732 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq729
       have r₂ := eq27
       grind)
    | exact resolve eq729 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq736 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq732 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq732
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq732
       grind)
    | exact resolve eq13 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq747 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq736
  have eq749 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq747 eq49
    | exact resolve eq49 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq747
  have eq753 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq749
    | exact resolve eq749 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq749
  have eq756 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq78 x x
       have i₂ := eq753
       grind)
    | exact superpose eq753 eq78
    | (have j0 := eq78 x x
       grind)
    | exact resolve eq78 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq757 : x = (M.op x x) := by grind
  clear eq756
  have eq796 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq757
       grind)
    | exact superpose eq757 eq53
    | exact resolve eq53 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq797 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq757
       grind)
    | exact superpose eq757 eq50
    | exact resolve eq50 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq798 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq757
       grind)
    | exact superpose eq757 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq757
       grind)
    | exact resolve eq13 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq799 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 x x X0
       have i₂ := eq757
       grind)
    | exact superpose eq757 eq14
    | exact resolve eq14 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq800 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq757
       grind)
    | exact superpose eq757 eq14
    | exact resolve eq14 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq811 : x = (k x x) := by grind
  clear eq798
  have eq813 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq811
       grind)
    | exact superpose eq811 eq43
    | exact resolve eq43 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq811
  have eq817 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq813
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq813
    | exact resolve eq813 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq813
  have eq835 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq817 eq78
    | (have j0 := eq78 x (σ x)
       grind)
    | exact resolve eq78 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq817
  have eq836 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq835
  have eq840 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq836 eq51
    | exact resolve eq51 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq836
  have eq946 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq800 (M.op x X0)
       have i₂ := eq799 X0
       grind)
    | exact superpose eq799 eq800
    | exact resolve eq800 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq949 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq796 eq800
    | exact resolve eq800 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq977 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq949 eq796
    | exact resolve eq796 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq949
  have eq995 : y = (M.op x y) := by
    first
    | exact superpose eq977 eq797
    | exact resolve eq797 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797 eq977
  have eq1008 : y = (M.op x y) := by
    first
    | (have i₁ := eq995
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq995
    | exact resolve eq995 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq995
  have eq1009 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1008 eq20
    | exact resolve eq20 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1008
  have eq1040 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1009
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1009
    | exact resolve eq1009 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1009
  have eq1042 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1040 eq26
    | exact resolve eq26 eq1040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1057 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq1040 eq840
    | exact resolve eq840 eq1040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840 eq1040
  have eq1289 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq799 X0
       have i₂ := eq946 X0
       grind)
    | exact superpose eq946 eq799
    | exact resolve eq799 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799 eq946
  have eq1315 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq800 X0
       have i₂ := eq1289 X0
       grind)
    | exact superpose eq1289 eq800
    | exact resolve eq800 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800 eq1289
  have eq1346 : ∀ X0 X1 : G, (M.op (M.op (M.op x X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 x X0
       have i₂ := eq1315 X0
       grind)
    | exact superpose eq1315 eq14
    | exact resolve eq14 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1369 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1346 X0 X1
       have i₂ := eq1315 X1
       grind)
    | exact superpose eq1315 eq1346
    | exact resolve eq1346 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315 eq1346
  have eq1627 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq1369
    | (have j0 := eq1369 (σ y) (σ x)
       grind)
    | exact resolve eq1369 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1369
  have eq1671 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1627 eq1057
    | exact resolve eq1057 eq1627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057 eq1627
  have eq1688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1042 eq1671
    | exact resolve eq1671 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042 eq1671
  have eq1690 : False := by grind
  exact eq1690

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_y_pyx_x_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
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
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq93 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq93 y x
       grind)
    | exact superpose eq93 eq75
    | (have j1 := eq93 x x
       grind)
    | exact resolve eq75 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq116
    | exact resolve eq116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq728 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq117 eq93
    | (have j0 := eq93 x (σ x)
       grind)
    | exact resolve eq93 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq729 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq728
    | exact resolve eq728 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq732 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq729
       have r₂ := eq27
       grind)
    | exact resolve eq729 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq736 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq732 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq732
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq732
       grind)
    | exact resolve eq13 eq732
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq732
  have eq747 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq736
  have eq749 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq747 eq49
    | exact resolve eq49 eq747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq747
  have eq753 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq749
    | exact resolve eq749 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq749
  have eq756 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq93 x x
       have i₂ := eq753
       grind)
    | exact superpose eq753 eq93
    | (have j0 := eq93 x x
       grind)
    | exact resolve eq93 eq753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq753
  have eq757 : x = (M.op x x) := by grind
  clear eq756
  have eq796 : x = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq53 x
       have i₂ := eq757
       grind)
    | exact superpose eq757 eq53
    | exact resolve eq53 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq797 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq50 x
       have i₂ := eq757
       grind)
    | exact superpose eq757 eq50
    | exact resolve eq50 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq798 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq757
       grind)
    | exact superpose eq757 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq757
       grind)
    | exact resolve eq13 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq799 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq14 x x X0
       have i₂ := eq757
       grind)
    | exact superpose eq757 eq14
    | exact resolve eq14 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq800 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 x x
       have i₂ := eq757
       grind)
    | exact superpose eq757 eq14
    | exact resolve eq14 eq757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757
  have eq811 : x = (k x x) := by grind
  clear eq798
  have eq813 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq811
       grind)
    | exact superpose eq811 eq43
    | exact resolve eq43 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq811
  have eq817 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq813
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq813
    | exact resolve eq813 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq813
  have eq835 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq817 eq93
    | (have j0 := eq93 x (σ x)
       grind)
    | exact resolve eq93 eq817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq817
  have eq836 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq835
  have eq840 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq836 eq51
    | exact resolve eq51 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq836
  have eq946 : ∀ X0 : G, (M.op x X0) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq800 (M.op x X0)
       have i₂ := eq799 X0
       grind)
    | exact superpose eq799 eq800
    | exact resolve eq800 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq949 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq796 eq800
    | exact resolve eq800 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq977 : x = (M.op (M.op x y) x) := by
    first
    | exact superpose eq949 eq796
    | exact resolve eq796 eq949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq949
  have eq995 : y = (M.op x y) := by
    first
    | exact superpose eq977 eq797
    | exact resolve eq797 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797 eq977
  have eq1008 : y = (M.op x y) := by
    first
    | (have i₁ := eq995
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq995
    | exact resolve eq995 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq995
  have eq1009 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1008 eq20
    | exact resolve eq20 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1008
  have eq1040 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1009
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1009
    | exact resolve eq1009 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1009
  have eq1042 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1040 eq26
    | exact resolve eq26 eq1040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1057 : (σ (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ (M.op x y))) := by
    first
    | exact superpose eq1040 eq840
    | exact resolve eq840 eq1040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq840 eq1040
  have eq1289 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq799 X0
       have i₂ := eq946 X0
       grind)
    | exact superpose eq946 eq799
    | exact resolve eq799 eq946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799 eq946
  have eq1315 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq800 X0
       have i₂ := eq1289 X0
       grind)
    | exact superpose eq1289 eq800
    | exact resolve eq800 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800 eq1289
  have eq1346 : ∀ X0 X1 : G, (M.op (M.op (M.op x X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 x X0
       have i₂ := eq1315 X0
       grind)
    | exact superpose eq1315 eq14
    | exact resolve eq14 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1369 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1346 X0 X1
       have i₂ := eq1315 X1
       grind)
    | exact superpose eq1315 eq1346
    | exact resolve eq1346 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315 eq1346
  have eq1627 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq26 eq1369
    | (have j0 := eq1369 (σ y) (σ x)
       grind)
    | exact resolve eq1369 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1369
  have eq1671 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1627 eq1057
    | exact resolve eq1057 eq1627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057 eq1627
  have eq1688 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1042 eq1671
    | exact resolve eq1671 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042 eq1671
  have eq1690 : False := by grind
  exact eq1690

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_y_x_pyy_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq50 : y ≠ (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
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
  have eq56 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq59 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq60 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) X0) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq82
    | exact resolve eq82 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq85 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq84
    | exact resolve eq84 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq108 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq16
    | exact resolve eq16 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq389 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq58 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq397 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq389 X0
       grind)
    | exact superpose eq389 eq14
    | exact resolve eq14 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op X0 X0) X0
       have i₂ := eq389 X0
       grind)
    | exact superpose eq389 eq13
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq389 X0
       grind)
    | exact resolve eq13 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389
  have eq400 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq399 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq611 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) X3) (σ X1)) X3) = X3 ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 (σ X1) (σ X0) X2 X3
       have i₂ := eq70 X0 X1
       grind)
    | exact superpose eq70 eq61
    | (have j1 := eq70 X1 X1
       grind)
    | exact resolve eq61 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq612 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op (σ X0) X2) (σ (k X0 X1))) X3) X2) X3) = X3 ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X2 (σ X0) (σ X1) X3
       have i₂ := eq70 X0 X1
       grind)
    | exact superpose eq70 eq61
    | (have j1 := eq70 X1 X1
       grind)
    | exact resolve eq61 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq619 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq70 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq621 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq619 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq954 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq397 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq397
    | exact resolve eq397 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq957 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq59 eq397
    | exact resolve eq397 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq960 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq60 eq397
    | exact resolve eq397 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq1007 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq960 eq13
    | (have j0 := eq13 (σ x) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq13 (σ x) (M.op (σ x) (σ y))
       have r₂ := eq960
       grind)
    | exact resolve eq13 eq960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq960
  have eq1017 : (σ x) = (k (σ x) (M.op (σ x) (σ y))) := by grind
  clear eq1007
  have eq4238 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq621 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq621
    | (have j0 := eq621 (τ X0)
       grind)
    | exact resolve eq621 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq621
  have eq4246 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4238 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4238
    | (have j0 := eq4238 X0
       grind)
    | exact resolve eq4238 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4238
  have eq4252 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4246 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4246
    | (have j0 := eq4246 X0
       grind)
    | exact resolve eq4246 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4246
  have eq8169 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq85 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8170 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq8169
    | exact resolve eq8169 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8169
  have eq8181 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq8170
       have r₂ := eq27
       grind)
    | exact resolve eq8170 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8170
  have eq8184 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq8181
    | exact resolve eq8181 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8181
  have eq8188 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq8184 eq400
    | exact resolve eq400 eq8184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq8184
  have eq8572 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq8188 eq108
    | exact resolve eq108 eq8188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq8188
  have eq8601 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq8572
    | exact resolve eq8572 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq8572
  have eq8602 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq4252 y
       grind)
    | (have r₁ := eq8601
       have r₂ := eq4252 y
       grind)
    | exact resolve eq8601 eq4252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4252 eq8601
  have eq8604 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq397 y X0
       have i₂ := eq8602
       grind)
    | exact superpose eq8602 eq397
    | exact resolve eq397 eq8602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8609 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq8602
       grind)
    | exact superpose eq8602 eq14
    | exact resolve eq14 eq8602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8602
  have eq8638 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8609 X0
       have i₂ := eq954 y X0
       grind)
    | exact superpose eq954 eq8609
    | exact resolve eq8609 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8609
  have eq10122 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8604 X0
       have i₂ := eq8638 X0
       grind)
    | exact superpose eq8638 eq8604
    | exact resolve eq8604 eq8638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8604
  have eq10180 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq10122 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10122
  have eq10228 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8638 X0
       have i₂ := eq10180 X0
       grind)
    | exact superpose eq10180 eq8638
    | exact resolve eq8638 eq10180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8638 eq10180
  have eq10311 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq10228 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10228
  have eq11846 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq10311 x
       grind)
    | exact superpose eq10311 eq18
    | (have j1 := eq10311 x
       grind)
    | exact resolve eq18 eq10311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10311
  have eq11899 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq11846
  have eq11942 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11899 eq1017
    | exact resolve eq1017 eq11899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1017 eq11899
  have eq11949 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11942 eq55
    | exact resolve eq55 eq11942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq11950 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11942 eq85
    | exact resolve eq85 eq11942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq11942
  have eq11959 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq11950
  have eq11968 : x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq11949
    | exact resolve eq11949 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11949
  have eq11974 : x = (k x y) := by
    first
    | (have r₁ := eq11968
       have r₂ := eq50
       grind)
    | exact resolve eq11968 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq11968
  have eq11977 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11974
       grind)
    | exact superpose eq11974 eq44
    | exact resolve eq44 eq11974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11974
  have eq11994 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq11977
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11977
    | exact resolve eq11977 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11977
  have eq12389 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq397 y X0
       have i₂ := eq11959
       grind)
    | exact superpose eq11959 eq397
    | exact resolve eq397 eq11959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12394 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq11959
       grind)
    | exact superpose eq11959 eq14
    | exact resolve eq14 eq11959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11959
  have eq12449 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq12394 X0
       have i₂ := eq954 y X0
       grind)
    | exact superpose eq954 eq12394
    | exact resolve eq12394 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12394
  have eq18197 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) X0) (k (σ x) (σ y))) X1) X0) X1) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq612 x y X0 X1
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq612
    | (have j0 := eq612 y y x x
       grind)
    | exact resolve eq612 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq18332 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq11994 eq18197
    | exact resolve eq18197 eq11994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18197
  have eq18446 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq18332 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18332
    | (have j0 := eq18332 X0 X1
       grind)
    | exact resolve eq18332 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18332
  have eq18557 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq18446 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18446
    | (have j0 := eq18446 X0 X1
       grind)
    | exact resolve eq18446 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18446
  have eq18651 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18557 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18557
    | (have j0 := eq18557 X0 X1
       grind)
    | exact resolve eq18557 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18557
  have eq18713 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18651 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq18651
    | (have j0 := eq18651 X0 X1
       grind)
    | exact resolve eq18651 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18651
  have eq18730 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq18713
    | (have j0 := eq18713 X0 X1
       grind)
    | exact resolve eq18713 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18713
  have eq18893 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (k (σ x) (σ y)) (M.op (σ x) X0)) X1) (σ y)) X1) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq611 x y X0 X1
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq611
    | (have j0 := eq611 y y x x
       grind)
    | exact resolve eq611 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq611
  have eq19222 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (k (σ x) (σ y)) (M.op (σ x) X0)) X1) (σ y)) X1) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq18893 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq18893
    | (have j0 := eq18893 X0 X1
       grind)
    | exact resolve eq18893 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18893
  have eq19385 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (k (σ x) (σ y)) (M.op (σ x) X0)) X1) (σ y)) X1) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq19222 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19222
    | (have j0 := eq19222 X0 X1
       grind)
    | exact resolve eq19222 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19222
  have eq19501 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (M.op (σ x) X0)) X1) (σ y)) X1) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq11994 eq19385
    | exact resolve eq19385 eq11994
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11994 eq19385
  have eq19608 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) X1) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq19501 X1 X1
       have i₂ := eq954 sF2 X1
       grind)
    | exact superpose eq954 eq19501
    | exact resolve eq19501 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19501
  have eq19704 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq19608 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19608
    | (have j0 := eq19608 X0 X1
       grind)
    | exact resolve eq19608 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19608
  have eq19768 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19704 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19704
    | (have j0 := eq19704 X0 X1
       grind)
    | exact resolve eq19704 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19704
  have eq19793 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19768 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19768
    | (have j0 := eq19768 X0 X1
       grind)
    | exact resolve eq19768 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19768
  have eq19804 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) X1) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq19793
    | (have j0 := eq19793 X0 X1
       grind)
    | exact resolve eq19793 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19793
  have eq24360 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19804 eq18730
    | exact resolve eq18730 eq19804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18730 eq19804
  have eq24416 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq24360
  have eq24421 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq24416
    | exact resolve eq24416 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24416
  have eq24422 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq24421
  have eq24426 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24422 eq397
    | exact resolve eq397 eq24422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq24431 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24422 eq14
    | exact resolve eq14 eq24422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24422
  have eq24503 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq24431 x
       have i₂ := eq954 sF3 x
       grind)
    | exact superpose eq954 eq24431
    | exact resolve eq24431 eq954
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954 eq24431
  have eq26642 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24503 eq24426
    | exact resolve eq24426 eq24503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24426
  have eq26726 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq26642 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26642
  have eq26970 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f26970_13 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f26970_14 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f26970_22 : (σ y) ≠ (M.op X0 (σ y)) := by grind
    have f26970_24 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f26970_25 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
      intro X0
      first
      | (have j0 := f26970_14 X0
         grind)
      | (have r₁ := f26970_14 X0
         have r₂ := f26970_24
         grind)
      | exact resolve f26970_14 f26970_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f26970_26 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) := by
      intro X0
      first
      | (have j0 := f26970_13 X0
         grind)
      | (have r₁ := f26970_13 X0
         have r₂ := f26970_24
         grind)
      | exact resolve f26970_13 f26970_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f26970_27 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
      intro X0
      first
      | (have i₁ := f26970_26 X0
         have i₂ := f26970_25 X0
         grind)
      | exact superpose f26970_25 f26970_26
      | exact resolve f26970_26 f26970_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f26970_28 : (σ y) ≠ (σ y) := by
      first
      | (have i₁ := f26970_22
         have i₂ := f26970_27 X0
         grind)
      | exact superpose f26970_27 f26970_22
      | (have r₁ := f26970_22
         have r₂ := f26970_27 X0
         grind)
      | exact resolve f26970_22 f26970_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f26970_29 : False := by grind
    exact f26970_29
  clear eq24503 eq26726
  have eq27086 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq26970 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26970
  have eq28352 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27086 eq26
    | (have j1 := eq27086 (σ x)
       grind)
    | exact resolve eq26 eq27086
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq27086
  have eq28407 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq28352
  have eq28783 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq28407 eq27
    | exact resolve eq27 eq28407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq28407
  have eq43558 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq12389 X0
       have i₂ := eq12449 X0
       grind)
    | exact superpose eq12449 eq12389
    | exact resolve eq12389 eq12449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12389
  have eq43659 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq43558 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43558
  have eq43750 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq12449 X0
       have i₂ := eq43659 X0
       grind)
    | exact superpose eq43659 eq12449
    | exact resolve eq12449 eq43659
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12449 eq43659
  have eq43886 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq43750 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43750
  have eq44562 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq43886 x
       grind)
    | exact superpose eq43886 eq18
    | (have j1 := eq43886 x
       grind)
    | exact resolve eq18 eq43886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43886
  have eq44664 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq44562
  have eq44691 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq44664 eq28
    | exact resolve eq28 eq44664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq44664
  have eq44906 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq44691
    | exact resolve eq44691 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq44691
  have eq44920 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44906 eq20
    | exact resolve eq20 eq44906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44906
  have eq45072 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44920
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq44920
    | exact resolve eq44920 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44920
  have eq45076 : x = (M.op x y) := by
    first
    | (have r₁ := eq45072
       have r₂ := eq28783
       grind)
    | exact resolve eq45072 eq28783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45072
  have eq45081 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq45076 eq20
    | exact resolve eq20 eq45076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq45172 : x = (M.op x x) := by
    first
    | exact superpose eq45076 eq957
    | exact resolve eq957 eq45076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq957
  have eq45254 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq45081
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45081
    | exact resolve eq45081 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45081
  have eq45494 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq45172
       grind)
    | exact superpose eq45172 eq56
    | exact resolve eq56 eq45172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq45625 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq45076 eq45494
    | exact resolve eq45494 eq45076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45494
  have eq45645 : y = (M.op x y) := by
    first
    | (have i₁ := eq45625
       have i₂ := eq45172
       grind)
    | exact superpose eq45172 eq45625
    | exact resolve eq45625 eq45172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45172 eq45625
  have eq45650 : y = (M.op x y) := by
    first
    | (have i₁ := eq45645
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq45645
    | exact resolve eq45645 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq45645
  have eq45651 : x = y := by
    first
    | exact superpose eq45076 eq45650
    | exact resolve eq45650 eq45076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45076 eq45650
  have eq45653 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq45651
       grind)
    | exact superpose eq45651 eq24
    | exact resolve eq24 eq45651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq45651
  have eq45859 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq45653
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45653
    | exact resolve eq45653 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq45653
  have eq45931 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq45254 eq45859
    | exact resolve eq45859 eq45254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45254 eq45859
  have eq45965 : False := by grind
  exact eq45965

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_y_x_x_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
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
  have eq50 : y ≠ (M.op x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq13
    | (have j0 := eq13 x y
       grind)
    | exact resolve eq13 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ x) (σ y)
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
  have eq56 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op x X0)) y) := by
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
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq59 : ∀ X0 : G, (M.op (M.op (M.op x X0) (M.op x y)) X0) = X0 := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X1 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
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
  have eq88 : (k y y) = (τ (k (σ y) (σ y))) := by
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
  have eq95 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X1)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq44
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq44 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq115
    | exact resolve eq115 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq117
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq117
    | exact resolve eq117 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq386 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq58 X0 x x X0
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq58
    | exact resolve eq58 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq394 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) X0
       have i₂ := eq386 X0
       grind)
    | exact superpose eq386 eq14
    | exact resolve eq14 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq396 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq13 (M.op X0 X0) X0
       have i₂ := eq386 X0
       grind)
    | exact superpose eq386 eq13
    | (have j0 := eq13 (M.op X0 X0) X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq386 X0
       grind)
    | exact resolve eq13 eq386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq397 : ∀ X0 : G, (M.op X0 X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq396 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396
  have eq607 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) X3) (σ X1)) X3) = X3 ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 (σ X1) (σ X0) X2 X3
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq61
    | (have j1 := eq95 X1 X1
       grind)
    | exact resolve eq61 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op (σ X0) X2) (σ (k X0 X1))) X3) X2) X3) = X3 ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X2 (σ X0) (σ X1) X3
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq61
    | (have j1 := eq95 X1 X1
       grind)
    | exact resolve eq61 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq614 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq95 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq616 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq614 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq614
  have eq945 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq394 X0 (M.op X0 X1)
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq394
    | exact resolve eq394 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq948 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq59 eq394
    | exact resolve eq394 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq4549 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq616 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq616
    | (have j0 := eq616 (τ X0)
       grind)
    | exact resolve eq616 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq616
  have eq4557 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq4549 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4549
    | (have j0 := eq4549 X0
       grind)
    | exact resolve eq4549 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4549
  have eq4563 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4557 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq4557
    | (have j0 := eq4557 X0
       grind)
    | exact resolve eq4557 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4557
  have eq10527 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq118 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10528 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq10527
    | exact resolve eq10527 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10527
  have eq10539 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq10528
       have r₂ := eq27
       grind)
    | exact resolve eq10528 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10528
  have eq10542 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq10539
    | exact resolve eq10539 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10539
  have eq10546 : (σ y) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq10542 eq397
    | exact resolve eq397 eq10542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397 eq10542
  have eq10818 : (τ (σ y)) = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq10546 eq88
    | exact resolve eq88 eq10546
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq10546
  have eq10853 : y = (k y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq10818
    | exact resolve eq10818 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq10818
  have eq10856 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have j1 := eq4563 y
       grind)
    | (have r₁ := eq10853
       have r₂ := eq4563 y
       grind)
    | exact resolve eq10853 eq4563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4563 eq10853
  have eq10861 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq70 X0 y
       have i₂ := eq10856
       grind)
    | exact superpose eq10856 eq70
    | (have j0 := eq70 X0 y
       grind)
    | (have r₁ := eq70 X0 y
       have r₂ := eq10856
       grind)
    | exact resolve eq70 eq10856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq10856
  have eq10900 : ∀ X0 : G, (k X0 y) = X0 ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq10861 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10861
  have eq11666 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq10900 x
       grind)
    | exact superpose eq10900 eq44
    | exact resolve eq44 eq10900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10900
  have eq11746 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11666
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11666
    | exact resolve eq11666 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11666
  have eq11767 : (σ x) = (k (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11746
       have r₂ := eq51
       grind)
    | exact resolve eq11746 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq11746
  have eq11776 : (τ (σ x)) = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11767 eq55
    | exact resolve eq55 eq11767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq11777 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11767 eq118
    | exact resolve eq118 eq11767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq11767
  have eq11786 : y = (M.op y y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq11777
  have eq11795 : x = (k x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq28 eq11776
    | exact resolve eq11776 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11776
  have eq11801 : x = (k x y) := by
    first
    | (have r₁ := eq11795
       have r₂ := eq50
       grind)
    | exact resolve eq11795 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq11795
  have eq11804 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq11801
       grind)
    | exact superpose eq11801 eq44
    | exact resolve eq44 eq11801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11801
  have eq11821 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq11804
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11804
    | exact resolve eq11804 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11804
  have eq12397 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq394 y X0
       have i₂ := eq11786
       grind)
    | exact superpose eq11786 eq394
    | exact resolve eq394 eq11786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12402 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq14 y y X0
       have i₂ := eq11786
       grind)
    | exact superpose eq11786 eq14
    | exact resolve eq14 eq11786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11786
  have eq12455 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq12402 X0
       have i₂ := eq945 y X0
       grind)
    | exact superpose eq945 eq12402
    | exact resolve eq12402 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12402
  have eq19277 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) X0) (k (σ x) (σ y))) X1) X0) X1) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq608 x y X0 X1
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq608
    | (have j0 := eq608 y y x x
       grind)
    | exact resolve eq608 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq19405 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq11821 eq19277
    | exact resolve eq19277 eq11821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19277
  have eq19521 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq19405 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19405
    | (have j0 := eq19405 X0 X1
       grind)
    | exact resolve eq19405 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19405
  have eq19630 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq19521 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19521
    | (have j0 := eq19521 X0 X1
       grind)
    | exact resolve eq19521 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19521
  have eq19721 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19630 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19630
    | (have j0 := eq19630 X0 X1
       grind)
    | exact resolve eq19630 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19630
  have eq19780 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19721 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq19721
    | (have j0 := eq19721 X0 X1
       grind)
    | exact resolve eq19721 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19721
  have eq19797 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ x)) X1) X0) X1) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq19780
    | (have j0 := eq19780 X0 X1
       grind)
    | exact resolve eq19780 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19780
  have eq19956 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (k (σ x) (σ y)) (M.op (σ x) X0)) X1) (σ y)) X1) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq607 x y X0 X1
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq607
    | (have j0 := eq607 y y x x
       grind)
    | exact resolve eq607 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq607
  have eq20275 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (k (σ x) (σ y)) (M.op (σ x) X0)) X1) (σ y)) X1) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq19956 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq19956
    | (have j0 := eq19956 X0 X1
       grind)
    | exact resolve eq19956 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19956
  have eq20443 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (k (σ x) (σ y)) (M.op (σ x) X0)) X1) (σ y)) X1) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq20275 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20275
    | (have j0 := eq20275 X0 X1
       grind)
    | exact resolve eq20275 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20275
  have eq20560 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) (M.op (σ x) X0)) X1) (σ y)) X1) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq11821 eq20443
    | exact resolve eq20443 eq11821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11821 eq20443
  have eq20667 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) X1) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq20560 X1 X1
       have i₂ := eq945 sF2 X1
       grind)
    | exact superpose eq945 eq20560
    | exact resolve eq20560 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20560
  have eq20760 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) X1) = X1 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq20667 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20667
    | (have j0 := eq20667 X0 X1
       grind)
    | exact resolve eq20667 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20667
  have eq20821 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20760 X0 X1
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20760
    | (have j0 := eq20760 X0 X1
       grind)
    | exact resolve eq20760 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20760
  have eq20846 : ∀ X0 X1 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20821 X0 X1
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20821
    | (have j0 := eq20821 X0 X1
       grind)
    | exact resolve eq20821 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20821
  have eq20857 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op (σ x) X0) X1) (σ y)) X1) = X1 ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq20846
    | (have j0 := eq20846 X0 X1
       grind)
    | exact resolve eq20846 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20846
  have eq24566 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20857 eq19797
    | exact resolve eq19797 eq20857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19797 eq20857
  have eq24620 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq24566
  have eq24623 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq24620
    | exact resolve eq24620 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24620
  have eq24624 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq24623
  have eq24627 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24624 eq394
    | exact resolve eq394 eq24624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394
  have eq24632 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op (σ y) X0)) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24624 eq14
    | exact resolve eq14 eq24624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24624
  have eq24703 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq24632 x
       have i₂ := eq945 sF3 x
       grind)
    | exact superpose eq945 eq24632
    | exact resolve eq24632 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945 eq24632
  have eq36638 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq24703 eq24627
    | exact resolve eq24627 eq24703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24627
  have eq36722 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq36638 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36638
  have eq36793 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f36793_14 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f36793_15 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) := by
      intro X0
      grind
    have f36793_24 : (σ y) ≠ (M.op X0 (σ y)) := by grind
    have f36793_26 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f36793_28 : ∀ X0 : G, (M.op (σ y) X0) = X0 := by
      intro X0
      first
      | (have j0 := f36793_15 X0
         grind)
      | (have r₁ := f36793_15 X0
         have r₂ := f36793_26
         grind)
      | exact resolve f36793_15 f36793_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f36793_29 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) X0) (σ y)) := by
      intro X0
      first
      | (have j0 := f36793_14 X0
         grind)
      | (have r₁ := f36793_14 X0
         have r₂ := f36793_26
         grind)
      | exact resolve f36793_14 f36793_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f36793_30 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
      intro X0
      first
      | (have i₁ := f36793_29 X0
         have i₂ := f36793_28 X0
         grind)
      | exact superpose f36793_28 f36793_29
      | exact resolve f36793_29 f36793_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f36793_31 : (σ y) ≠ (σ y) := by
      first
      | (have i₁ := f36793_24
         have i₂ := f36793_30 X0
         grind)
      | exact superpose f36793_30 f36793_24
      | (have r₁ := f36793_24
         have r₂ := f36793_30 X0
         grind)
      | exact resolve f36793_24 f36793_30
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f36793_32 : False := by grind
    exact f36793_32
  clear eq24703 eq36722
  have eq36909 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have j0 := eq36793 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36793
  have eq37987 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36909 eq26
    | (have j1 := eq36909 (σ x)
       grind)
    | exact resolve eq26 eq36909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq36909
  have eq38039 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq37987
  have eq38054 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq38039 eq27
    | exact resolve eq27 eq38039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq38039
  have eq143423 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq12397 X0
       have i₂ := eq12455 X0
       grind)
    | exact superpose eq12455 eq12397
    | exact resolve eq12397 eq12455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12397
  have eq143531 : ∀ X0 : G, (M.op y X0) = X0 ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq143423 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143423
  have eq144490 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq12455 X0
       have i₂ := eq143531 X0
       grind)
    | exact superpose eq143531 eq12455
    | exact resolve eq12455 eq143531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12455 eq143531
  have eq144643 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq144490 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144490
  have eq147248 : y = (M.op x y) ∨ y = (M.op x y) ∨ (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq144643 x
       grind)
    | exact superpose eq144643 eq18
    | (have j1 := eq144643 x
       grind)
    | exact resolve eq18 eq144643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144643
  have eq147351 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq147248
  have eq147373 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq147351 eq28
    | exact resolve eq28 eq147351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq147351
  have eq147667 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq147373
    | exact resolve eq147373 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq147373
  have eq147686 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq147667 eq20
    | exact resolve eq20 eq147667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147667
  have eq147987 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq147686
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq147686
    | exact resolve eq147686 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147686
  have eq147997 : x = (M.op x y) := by
    first
    | (have r₁ := eq147987
       have r₂ := eq38054
       grind)
    | exact resolve eq147987 eq38054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147987
  have eq148002 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq147997 eq20
    | exact resolve eq20 eq147997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq148097 : x = (M.op x x) := by
    first
    | exact superpose eq147997 eq948
    | exact resolve eq948 eq147997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq148330 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq148002
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq148002
    | exact resolve eq148002 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148002
  have eq148659 : y = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq56 x
       have i₂ := eq148097
       grind)
    | exact superpose eq148097 eq56
    | exact resolve eq56 eq148097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq148801 : y = (M.op (M.op x x) y) := by
    first
    | exact superpose eq147997 eq148659
    | exact resolve eq148659 eq147997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148659
  have eq148821 : y = (M.op x y) := by
    first
    | (have i₁ := eq148801
       have i₂ := eq148097
       grind)
    | exact superpose eq148097 eq148801
    | exact resolve eq148801 eq148097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148097 eq148801
  have eq148826 : y = (M.op x y) := by
    first
    | (have i₁ := eq148821
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq148821
    | exact resolve eq148821 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq148821
  have eq148827 : x = y := by
    first
    | exact superpose eq147997 eq148826
    | exact resolve eq148826 eq147997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147997 eq148826
  have eq148829 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq148827
       grind)
    | exact superpose eq148827 eq24
    | exact resolve eq24 eq148827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq148827
  have eq149332 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq148829
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq148829
    | exact resolve eq148829 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq148829
  have eq149467 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq148330 eq149332
    | exact resolve eq149332 eq148330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148330 eq149332
  have eq149530 : False := by grind
  exact eq149530

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxx_pyx_pyx_pxx_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  clear eq18
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
  clear eq33 eq38
  have eq81 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
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
  have eq85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq92 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq40 X1
       grind)
    | exact superpose eq40 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq94 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq92
    | (have j0 := eq92 X0 X1
       grind)
    | exact resolve eq92 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq92
  have eq229 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq94 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq94
    | exact resolve eq94 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq262 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq229 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq229
    | (have j0 := eq229 X0 X1
       grind)
    | exact resolve eq229 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq229
  have eq269 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq262 X0 X1
       have j1 := eq81 X1 X0
       grind)
    | (have r₁ := eq262 X1 (τ X1)
       have r₂ := eq81 (τ X1) X1
       grind)
    | (have r₁ := eq262 X1 X0
       have r₂ := eq81 X0 X1
       grind)
    | exact resolve eq262 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq262
  have eq273 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq269 X0 X1
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq269
    | (have j0 := eq269 X0 X1
       grind)
    | exact resolve eq269 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq269
  have eq778 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq273 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq273
    | exact resolve eq273 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq273
  have eq1368 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X1
       have i₂ := eq778 X0 X1
       grind)
    | (have i₁ := eq12 X1 X0
       have i₂ := eq778 X0 X1
       grind)
    | exact superpose eq778 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq778 X1 X0
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq778 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq778 X1 X1
       grind)
    | exact resolve eq12 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1369 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X1
       have i₂ := eq778 X0 X1
       grind)
    | (have i₁ := eq13 X1 X0
       have i₂ := eq778 X0 X1
       grind)
    | exact superpose eq778 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq778 X1 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq778 X0 X0
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq778 X0 X1
       grind)
    | exact resolve eq13 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1435 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1369 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq1465 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1368 X0 X1
       have j1 := eq1435 X0 X1
       grind)
    | (have r₁ := eq1368 X0 X1
       have r₂ := eq1435 X0 X1
       grind)
    | (have r₁ := eq1368 X1 X0
       have r₂ := eq1435 X0 X1
       grind)
    | exact resolve eq1368 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1368 eq1435
  have eq2260 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1465 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1465
  have eq2270 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2260 X0 X1
       have j1 := eq778 X1 X0
       grind)
    | (have r₁ := eq2260 X0 X0
       have r₂ := eq778 X0 X0
       grind)
    | (have r₁ := eq2260 X1 X0
       have r₂ := eq778 X0 X1
       grind)
    | exact resolve eq2260 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778 eq2260
  have eq2324 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2270 (σ X1) (σ X0)
       grind)
    | exact superpose eq2270 eq15
    | exact resolve eq15 eq2270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2343 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2324 X0 X1
       have i₂ := eq2270 X1 X0
       grind)
    | exact superpose eq2270 eq2324
    | exact resolve eq2324 eq2270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2270 eq2324
  have eq3198 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2343 x y
       grind)
    | exact superpose eq2343 eq16
    | (have r₁ := eq16
       have r₂ := eq2343 x y
       grind)
    | exact resolve eq16 eq2343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2343
  have eq3255 : False := by grind
  exact eq3255

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pyx_pyy_pyx_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq64 (σ X0)
       grind)
    | exact superpose eq64 eq15
    | exact resolve eq15 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq64 (τ X0)
       grind)
    | exact superpose eq64 eq32
    | exact resolve eq32 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq76 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq69
    | exact resolve eq69 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq67
    | exact resolve eq67 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq67
  have eq93 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq9
    | exact resolve eq9 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq62 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq193 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq185 X0
       grind)
    | exact superpose eq185 eq9
    | exact resolve eq9 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq248 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq193 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq193
    | exact resolve eq193 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq193 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq93 X0 (σ X0)
       grind)
    | exact superpose eq93 eq193
    | exact resolve eq193 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq193
  have eq1898 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq1921 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1898 X0 X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq1898
    | (have j0 := eq1898 X0 X1
       grind)
    | exact resolve eq1898 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1898
  have eq1941 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1921 X0 X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq1921
    | (have j0 := eq1921 X0 X1
       grind)
    | exact resolve eq1921 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq1921
  have eq4151 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1941 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1941
    | exact resolve eq1941 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1941
  have eq4303 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4151 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq4151
    | (have j0 := eq4151 X0 X1
       grind)
    | exact resolve eq4151 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4151
  have eq4321 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq4303 X0 X1
       have j1 := eq95 X1 X0
       grind)
    | (have r₁ := eq4303 (M.op (σ X0) X1) X0
       have r₂ := eq95 X0 X1
       grind)
    | (have r₁ := eq4303 X1 X0
       have r₂ := eq95 X0 X1
       grind)
    | exact resolve eq4303 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq4303
  have eq4345 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4321 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq4321
    | (have j0 := eq4321 X1 (τ X0)
       grind)
    | exact resolve eq4321 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4368 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq4321 (σ X1) X0
       grind)
    | exact superpose eq4321 eq15
    | (have j1 := eq4321 (σ X1) X0
       grind)
    | exact resolve eq15 eq4321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4321
  have eq4395 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq4345 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq4345
    | (have j0 := eq4345 X0 X1
       grind)
    | exact resolve eq4345 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq4345
  have eq4397 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4395 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq4395
    | (have j0 := eq4395 X0 X1
       grind)
    | exact resolve eq4395 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4395
  have eq4423 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq4397 X0 (τ X1)
       grind)
    | exact superpose eq4397 eq18
    | (have j1 := eq4397 X0 (τ X1)
       grind)
    | exact resolve eq18 eq4397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq4397
  have eq4920 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4423 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4423
    | exact resolve eq4423 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4423
  have eq5130 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4920 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4920
    | (have j0 := eq4920 X0 X1
       grind)
    | exact resolve eq4920 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4920
  have eq5525 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4368 x y
       grind)
    | exact superpose eq4368 eq16
    | (have j1 := eq4368 x y
       grind)
    | exact resolve eq16 eq4368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4368
  have eq5805 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5525
       have i₂ := eq5130 y x
       grind)
    | exact superpose eq5130 eq5525
    | (have j1 := eq5130 y x
       grind)
    | (have r₁ := eq5525
       have r₂ := eq5130 y x
       grind)
    | exact resolve eq5525 eq5130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5130 eq5525
  have eq5806 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq5805
  have eq5827 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq5806
       grind)
    | exact superpose eq5806 eq10
    | exact resolve eq10 eq5806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5806
  have eq5892 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq5827
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq5827
    | exact resolve eq5827 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5827
  have eq5893 : y = (M.op x x) := by grind
  clear eq5892
  have eq5931 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq250 x
       have i₂ := eq5893
       grind)
    | exact superpose eq5893 eq250
    | exact resolve eq250 eq5893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250
  have eq5970 : y = (M.op x y) := by
    first
    | (have i₁ := eq248 x x
       have i₂ := eq5893
       grind)
    | exact superpose eq5893 eq248
    | exact resolve eq248 eq5893
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq5893
  have eq6187 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5931
       grind)
    | exact superpose eq5931 eq16
    | exact resolve eq16 eq5931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5931
  have eq6231 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq6187
       have i₂ := eq5970
       grind)
    | exact superpose eq5970 eq6187
    | exact resolve eq6187 eq5970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5970 eq6187
  have eq6232 : False := by grind
  exact eq6232

/-- `Equation2712`: `x = ((y ◇ x) ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,Y) else if m(X,X) = X then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_x_pyy_y_pxy_Equation2712 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2712 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2712.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
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
  have eq31 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3)) X0) = X0 := by
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
  have eq32 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X1 X0) (M.op X1 X2)) X3) X0) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X0) (M.op X1 X2)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq22
  have eq68 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq31 X0 x x X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (M.op (M.op X0 X0) X1) X0) X2)) X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X1 (M.op X0 X0) X0 X2
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq31
    | exact resolve eq31 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq76 : ∀ X0 X1 : G, (M.op (M.op (M.op (M.op X0 X0) X1) X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (M.op X0 X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 (M.op X0 X0) X1
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq9
    | exact resolve eq9 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq90 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (M.op X0 X1)
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq76
    | exact resolve eq76 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq14
    | (have j0 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq14 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq225 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op (M.op X0 X1) (M.op X0 X2)) X3) (M.op X0 X1)) X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq32 (M.op X0 X1) X0 X2 X3
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq32
    | exact resolve eq32 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq349 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq113 x y
       grind)
    | exact superpose eq113 eq16
    | (have j1 := eq113 x x
       grind)
    | exact resolve eq16 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq351 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ X0) X2) (σ (k X0 X1))) X2) = X2 ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (σ X0) (σ X1)
       have i₂ := eq113 X0 X1
       grind)
    | exact superpose eq113 eq9
    | (have j1 := eq113 X0 X0
       grind)
    | exact resolve eq9 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq113 X0 X1
       grind)
    | exact superpose eq113 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq113 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq113 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq113 X0 X1
       grind)
    | exact resolve eq12 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq113 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq369 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq368 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq377 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq352 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq352
    | (have j0 := eq352 X0 X1
       grind)
    | exact resolve eq352 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq384 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq369 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq369
    | (have j0 := eq369 (τ X0)
       grind)
    | exact resolve eq369 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq369
  have eq386 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq384 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq384
    | (have j0 := eq384 X0
       grind)
    | exact resolve eq384 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384
  have eq389 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq386 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq386
    | (have j0 := eq386 X0
       grind)
    | exact resolve eq386 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq386
  have eq493 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X2)) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq73 X0 (M.op X0 X1) X2
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq73
    | exact resolve eq73 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq4317 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq349
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq349
    | (have j1 := eq14 (σ x) (σ x)
       grind)
    | exact resolve eq349 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq349
  have eq4320 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq4317
  have eq4991 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (τ X0)) X2) (σ (τ (k X0 X1)))) X2) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq351 (τ X0) (τ X1) X2
       have i₂ := eq33 X1 X0
       grind)
    | exact superpose eq33 eq351
    | (have j0 := eq351 (τ X0) (τ X0) X2
       grind)
    | exact resolve eq351 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq351
  have eq5094 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (τ X0)) X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4991 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq4991
    | (have j0 := eq4991 X0 X0 X2
       grind)
    | exact resolve eq4991 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4991
  have eq5101 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5094 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5094
    | (have j0 := eq5094 X0 X0 X2
       grind)
    | exact resolve eq5094 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5094
  have eq5107 : ∀ X0 X1 X2 : G, (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 X2) (k X0 X1)) X2) = X2 ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5101 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5101
    | (have j0 := eq5101 X0 X1 X2
       grind)
    | exact resolve eq5101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5101
  have eq5112 : ∀ X0 X1 X2 : G, (σ (τ X1)) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op (M.op (M.op X0 X2) (k X0 X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5107 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5107
    | (have j0 := eq5107 X0 X1 X2
       grind)
    | exact resolve eq5107 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5107
  have eq5117 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X2) (k X0 X1)) X2) = X2 ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5112 X0 X0 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5112
    | (have j0 := eq5112 X0 X1 X2
       grind)
    | exact resolve eq5112 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5112
  have eq12333 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 (k X0 X1)) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (k X0 X1)
       have i₂ := eq5117 X0 X1 X0
       grind)
    | exact superpose eq5117 eq76
    | (have j1 := eq5117 X0 X0 x
       grind)
    | exact resolve eq76 eq5117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5117
  have eq20185 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq90 (σ y) (σ x)
       have i₂ := eq4320
       grind)
    | exact superpose eq4320 eq90
    | exact resolve eq90 eq4320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4320
  have eq195656 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq107 (σ y) (σ y)
       have i₂ := eq20185
       grind)
    | exact superpose eq20185 eq107
    | (have r₁ := eq107 (σ y) (σ y)
       have r₂ := eq20185
       grind)
    | (have r₁ := eq107 (σ x) (σ x)
       have r₂ := eq20185
       grind)
    | (have r₁ := eq107 x x
       have r₂ := eq20185
       grind)
    | exact resolve eq107 eq20185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20185
  have eq195873 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq195656
  have eq195963 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq195873
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq195873
    | exact resolve eq195873 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195873
  have eq196094 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq107 (σ x) (σ x)
       have i₂ := eq195963
       grind)
    | exact superpose eq195963 eq107
    | (have r₁ := eq107 (σ x) (σ x)
       have r₂ := eq195963
       grind)
    | (have r₁ := eq107 x x
       have r₂ := eq195963
       grind)
    | (have r₁ := eq107 y x
       have r₂ := eq195963
       grind)
    | exact resolve eq107 eq195963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195963
  have eq196311 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (σ (k y y)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq196094
  have eq196401 : (σ y) = (σ (k y y)) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq196311
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq196311
    | exact resolve eq196311 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196311
  have eq196491 : (τ (σ y)) = (k y y) ∨ (σ x) = (σ (k x x)) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq196401
       grind)
    | exact superpose eq196401 eq10
    | exact resolve eq10 eq196401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196401
  have eq196658 : (σ x) = (σ (k x x)) ∨ y = (k y y) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq196491
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq196491
    | exact resolve eq196491 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196491
  have eq196707 : (τ (σ x)) = (k x x) ∨ y = (k y y) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq10 (k x x)
       have i₂ := eq196658
       grind)
    | exact superpose eq196658 eq10
    | exact resolve eq10 eq196658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196658
  have eq196874 : x = (k x x) ∨ y = (k y y) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq196707
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq196707
    | exact resolve eq196707 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196707
  have eq196882 : y = (k y y) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq389 x
       grind)
    | (have r₁ := eq196874
       have r₂ := eq389 x
       grind)
    | (have r₁ := eq196874
       have r₂ := eq389 y
       grind)
    | exact resolve eq196874 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq196874
  have eq197078 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq12333 y y
       have i₂ := eq196882
       grind)
    | exact superpose eq196882 eq12333
    | (have j0 := eq12333 y y
       grind)
    | exact resolve eq12333 eq196882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12333 eq196882
  have eq197168 : y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op y x) := by grind
  clear eq197078
  have eq197277 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq197168
       grind)
    | exact superpose eq197168 eq76
    | exact resolve eq76 eq197168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197375 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq493 y y x
       have i₂ := eq197168
       grind)
    | exact superpose eq197168 eq493
    | exact resolve eq493 eq197168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197168
  have eq197648 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq197375 X0
       have i₂ := eq90 y X0
       grind)
    | exact superpose eq90 eq197375
    | exact resolve eq197375 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197375
  have eq200241 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x x) ∨ y = (M.op y x) ∨ x = (M.op x x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq197277 X0
       have i₂ := eq197648 X0
       grind)
    | exact superpose eq197648 eq197277
    | exact resolve eq197277 eq197648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197277 eq197648
  have eq200739 : ∀ X0 : G, y = (M.op y x) ∨ x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq200241 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200241
  have eq200805 : ∀ X0 : G, y = (M.op y y) ∨ x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq90 y x
       have i₂ := eq200739 X0
       grind)
    | exact superpose eq200739 eq90
    | (have j1 := eq200739 y
       grind)
    | exact resolve eq90 eq200739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200739
  have eq201182 : y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq200805 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200805
  have eq201310 : ∀ X0 : G, (M.op (M.op (M.op y X0) y) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq76 y X0
       have i₂ := eq201182
       grind)
    | exact superpose eq201182 eq76
    | exact resolve eq76 eq201182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201385 : y ≠ y ∨ y = (k y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq107 y y
       have i₂ := eq201182
       grind)
    | exact superpose eq201182 eq107
    | (have r₁ := eq107 y y
       have r₂ := eq201182
       grind)
    | (have r₁ := eq107 x x
       have r₂ := eq201182
       grind)
    | exact resolve eq107 eq201182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq201408 : ∀ X0 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq493 y y x
       have i₂ := eq201182
       grind)
    | exact superpose eq201182 eq493
    | exact resolve eq493 eq201182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201182
  have eq201602 : y = (k y y) ∨ x = (M.op x x) := by grind
  clear eq201385
  have eq201684 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq201408 X0
       have i₂ := eq90 y X0
       grind)
    | exact superpose eq90 eq201408
    | exact resolve eq201408 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201408
  have eq201919 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq377 y y
       have i₂ := eq201602
       grind)
    | exact superpose eq201602 eq377
    | (have j0 := eq377 y y
       grind)
    | exact resolve eq377 eq201602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201602
  have eq202044 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq201919
  have eq202045 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq202044
  have eq203079 : ∀ X0 : G, (M.op (M.op (M.op (σ y) X0) (σ y)) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq76 (σ y) X0
       have i₂ := eq202045
       grind)
    | exact superpose eq202045 eq76
    | exact resolve eq76 eq202045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202045
  have eq204643 : ∀ X0 : G, (M.op y X0) = X0 ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq201310 X0
       have i₂ := eq201684 X0
       grind)
    | exact superpose eq201684 eq201310
    | exact resolve eq201310 eq201684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201310 eq201684
  have eq205143 : ∀ X0 : G, x = (M.op x x) ∨ (M.op y X0) = X0 := by
    intro X0
    first
    | (have j0 := eq204643 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204643
  have eq205190 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) x) X0) = X0 ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq76 x X0
       have i₂ := eq205143 X1
       grind)
    | exact superpose eq205143 eq76
    | (have j1 := eq205143 X1
       grind)
    | exact resolve eq76 eq205143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205288 : ∀ X0 X1 : G, x = (M.op (M.op x (M.op x X0)) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq493 x x x
       have i₂ := eq205143 X0
       grind)
    | exact superpose eq205143 eq493
    | (have j1 := eq205143 X1
       grind)
    | exact resolve eq493 eq205143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205143
  have eq205561 : ∀ X0 X1 : G, x = (M.op (M.op x X0) x) ∨ (M.op y X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq205288 X0 X1
       have i₂ := eq90 x X0
       grind)
    | exact superpose eq90 eq205288
    | (have j0 := eq205288 X0 X1
       grind)
    | exact resolve eq205288 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205288
  have eq208488 : ∀ X0 X1 X2 : G, (M.op x X0) = X0 ∨ (M.op y X1) = X1 ∨ (M.op y X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq205190 X0 X1
       have i₂ := eq205561 X0 X2
       grind)
    | exact superpose eq205561 eq205190
    | (have j0 := eq205190 X0 X1
       have j1 := eq205561 X0 X1
       grind)
    | exact resolve eq205190 eq205561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205190 eq205561
  have eq208986 : ∀ X0 X1 : G, (M.op y X0) = X0 ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq208488 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208488
  have eq209040 : ∀ X0 X1 : G, y = (M.op (M.op y (M.op y X0)) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq77 y X0
       have i₂ := eq208986 y X1
       grind)
    | exact superpose eq208986 eq77
    | (have j1 := eq208986 X0 X1
       grind)
    | exact resolve eq77 eq208986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq209087 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op y X1)) X0) = X0 ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 y X1
       have i₂ := eq208986 X0 X2
       grind)
    | exact superpose eq208986 eq9
    | (have j1 := eq208986 X0 X2
       grind)
    | exact resolve eq9 eq208986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq209804 : ∀ X0 X1 : G, y = (M.op (M.op y X0) y) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq209040 X0 X1
       have i₂ := eq90 y X0
       grind)
    | exact superpose eq90 eq209040
    | (have j0 := eq209040 X0 X1
       grind)
    | exact resolve eq209040 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209040
  have eq214213 : ∀ X0 X1 X2 : G, y = (M.op X0 y) ∨ (M.op x X1) = X1 ∨ (M.op x X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq209804 X0 X1
       have i₂ := eq208986 X0 X2
       grind)
    | exact superpose eq208986 eq209804
    | (have j0 := eq209804 X0 X1
       have j1 := eq208986 X0 X1
       grind)
    | exact resolve eq209804 eq208986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209804
  have eq214842 : ∀ X0 X1 : G, y = (M.op X1 y) ∨ (M.op x X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq214213 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214213
  have eq216342 : y ≠ y ∨ y = (M.op x y) := by
    first
    | (have j0 := eq214842 y x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214842
  have eq216343 : y = (M.op x y) := by grind
  clear eq216342
  have eq244672 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) X1) = X1 ∨ (M.op x X2) = X2 ∨ (M.op x X3) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq209087 X1 X0 X2
       have i₂ := eq208986 X0 X3
       grind)
    | exact superpose eq208986 eq209087
    | (have j0 := eq209087 X0 X1 X2
       have j1 := eq208986 X0 X2
       grind)
    | exact resolve eq209087 eq208986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208986 eq209087
  have eq245818 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X1) = X1 ∨ (M.op x X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq244672 X2 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244672
  have eq310611 : ∀ X0 X1 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x x) ∨ (M.op x X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq203079 X0
       have i₂ := eq245818 X1 (σ y) X0
       grind)
    | exact superpose eq245818 eq203079
    | (have j1 := eq245818 x X1 x
       grind)
    | exact resolve eq203079 eq245818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203079
  have eq311221 : ∀ X0 : G, (M.op (σ y) X0) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq310611 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq310611
  have eq311732 : ∀ X0 X1 : G, (σ y) = (M.op X0 (σ y)) ∨ (M.op x X1) = X1 ∨ x = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq245818 X1 (σ y) X0
       have i₂ := eq311221 X0
       grind)
    | exact superpose eq311221 eq245818
    | (have j0 := eq245818 X1 X1 x
       grind)
    | exact resolve eq245818 eq311221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245818 eq311221
  have eq312220 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq311732 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311732
  have eq313909 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq312220 (σ x)
       grind)
    | exact superpose eq312220 eq16
    | exact resolve eq16 eq312220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312220
  have eq314153 : (σ y) ≠ (σ y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq313909
       have i₂ := eq216343
       grind)
    | exact superpose eq216343 eq313909
    | exact resolve eq313909 eq216343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313909
  have eq314154 : x = (M.op x x) := by grind
  clear eq314153
  have eq315842 : ∀ X0 : G, (M.op (M.op (M.op x X0) x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq76 x X0
       have i₂ := eq314154
       grind)
    | exact superpose eq314154 eq76
    | exact resolve eq76 eq314154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq315919 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq107 x x
       have i₂ := eq314154
       grind)
    | exact superpose eq314154 eq107
    | (have r₁ := eq107 x x
       have r₂ := eq314154
       grind)
    | exact resolve eq107 eq314154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq315942 : ∀ X0 : G, x = (M.op (M.op x (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq493 x x x
       have i₂ := eq314154
       grind)
    | exact superpose eq314154 eq493
    | exact resolve eq493 eq314154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314154
  have eq316185 : x = (k x x) := by grind
  clear eq315919
  have eq316289 : ∀ X0 : G, x = (M.op (M.op x X0) x) := by
    intro X0
    first
    | (have i₁ := eq315942 X0
       have i₂ := eq90 x X0
       grind)
    | exact superpose eq90 eq315942
    | exact resolve eq315942 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq315942
  have eq316542 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq377 x x
       have i₂ := eq316185
       grind)
    | exact superpose eq316185 eq377
    | (have j0 := eq377 x x
       grind)
    | exact resolve eq377 eq316185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq316185
  have eq316667 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq316542
  have eq316668 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq316667
  have eq327403 : ∀ X0 : G, (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq315842 X0
       have i₂ := eq316289 X0
       grind)
    | exact superpose eq316289 eq315842
    | exact resolve eq315842 eq316289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq315842 eq316289
  have eq327522 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op x X1) X0) X2) (M.op x X1)) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq225 x X1 X0 X2
       have i₂ := eq327403 X0
       grind)
    | exact superpose eq327403 eq225
    | exact resolve eq225 eq327403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq327537 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op (M.op x X1) X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq493 x X1 X0
       have i₂ := eq327403 X0
       grind)
    | exact superpose eq327403 eq493
    | exact resolve eq493 eq327403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq328760 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq327537 X0 X0
       have i₂ := eq327403 X0
       grind)
    | exact superpose eq327403 eq327537
    | exact resolve eq327537 eq327403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327537
  have eq328774 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X1 X0) X2) X1) X2) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq327522 X0 X0 X2
       have i₂ := eq327403 X0
       grind)
    | exact superpose eq327403 eq327522
    | exact resolve eq327522 eq327403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327403 eq327522
  have eq395125 : ∀ X0 : G, (M.op (M.op (M.op (σ x) X0) (σ x)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq328774 (σ x) (σ x) X0
       have i₂ := eq316668
       grind)
    | exact superpose eq316668 eq328774
    | exact resolve eq328774 eq316668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316668 eq328774
  have eq396814 : ∀ X0 : G, (M.op (σ x) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq395125 X0
       have i₂ := eq328760 X0 (σ x)
       grind)
    | exact superpose eq328760 eq395125
    | exact resolve eq395125 eq328760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq328760 eq395125
  have eq398293 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq396814 (σ y)
       grind)
    | exact superpose eq396814 eq16
    | exact resolve eq16 eq396814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396814
  have eq399546 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq398293
       have i₂ := eq216343
       grind)
    | exact superpose eq216343 eq398293
    | exact resolve eq398293 eq216343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216343 eq398293
  have eq399547 : False := by grind
  exact eq399547
