import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation643`: `x = x ◇ (y ◇ ((y ◇ y) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_x_pxy_Equation643 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law643 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law643.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X1) X1))) = X0 := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X1) (σ X1)) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq57 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq65 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ (M.op X0 X0)) (σ X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq9
    | exact resolve eq9 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq57 X1 X0
       grind)
    | exact superpose eq57 eq10
    | (have j1 := eq57 X1 X0
       grind)
    | exact resolve eq10 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq214 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq203 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq203
    | (have j0 := eq203 X0 X1
       grind)
    | exact resolve eq203 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq285 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65 (M.op X0 (M.op (M.op X0 X0) X0)) X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq324 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq285 X0 X1
       have i₂ := eq22 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq22 eq285
    | exact resolve eq285 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq332 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op (M.op X0 X0) X0))) (σ (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq324 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq324
    | exact resolve eq324 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324
  have eq336 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op (M.op X0 X0) X0)) (M.op X0 (M.op (M.op X0 X0) X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq332 X0 X1
       have i₂ := eq22 (M.op X0 (M.op (M.op X0 X0) X0))
       grind)
    | exact superpose eq22 eq332
    | exact resolve eq332 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq340 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op (M.op X0 X0) X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq336 X0 X1
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X0) X0)) X0
       grind)
    | exact superpose eq9 eq336
    | exact resolve eq336 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq1119 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq53 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq53
    | (have j0 := eq53 X0 X1
       grind)
    | exact resolve eq53 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1179 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1119 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1119
    | (have j0 := eq1119 (M.op X1 X1) X1
       grind)
    | exact resolve eq1119 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq1976 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq214 y x
       grind)
    | exact superpose eq214 eq16
    | (have j1 := eq214 y x
       grind)
    | exact resolve eq16 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq18683 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq1976
       have i₂ := eq1179 x y
       grind)
    | exact superpose eq1179 eq1976
    | (have j1 := eq1179 (M.op y y) y
       grind)
    | (have r₁ := eq1976
       have r₂ := eq1179 x y
       grind)
    | (have r₁ := eq1976
       have r₂ := eq1179 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1976
       have r₂ := eq1179 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1976 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1179 eq1976
  have eq18684 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18683
  have eq18685 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq18684
  have eq18689 : ∀ X0 : G, (M.op X0 (M.op y (M.op y y))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq9 X0 y
       have i₂ := eq18685
       grind)
    | exact superpose eq18685 eq9
    | exact resolve eq9 eq18685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18714 : ∀ X0 : G, (M.op X0 (σ (M.op y (M.op y y)))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq340 y X0
       have i₂ := eq18685
       grind)
    | exact superpose eq18685 eq340
    | exact resolve eq340 eq18685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq19309 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18689 X0
       have i₂ := eq18685
       grind)
    | exact superpose eq18685 eq18689
    | exact resolve eq18689 eq18685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18685
  have eq19391 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq19309 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19309
  have eq19716 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18689 X0
       have i₂ := eq19391 y
       grind)
    | exact superpose eq19391 eq18689
    | exact resolve eq18689 eq19391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18689
  have eq19717 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq19716 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19716
  have eq20985 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq18714 X0
       have i₂ := eq19391 y
       grind)
    | exact superpose eq19391 eq18714
    | exact resolve eq18714 eq19391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18714 eq19391
  have eq21092 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq20985 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20985
  have eq21624 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq21092 (σ x)
       grind)
    | exact superpose eq21092 eq16
    | exact resolve eq16 eq21092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21092
  have eq22528 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq21624
       have i₂ := eq19717 x
       grind)
    | exact superpose eq19717 eq21624
    | exact resolve eq21624 eq19717
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19717 eq21624
  have eq22529 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq22528
  have eq22530 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq22529
  have eq22841 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq22530
       grind)
    | exact superpose eq22530 eq10
    | exact resolve eq10 eq22530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22530
  have eq22913 : x = y ∨ x = y := by
    first
    | (have i₁ := eq22841
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22841
    | exact resolve eq22841 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22841
  have eq22914 : x = y := by grind
  clear eq22913
  have eq23192 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22914
       grind)
    | exact superpose eq22914 eq16
    | exact resolve eq16 eq22914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22914
  have eq23193 : False := by grind
  exact eq23193

/-- `Equation646`: `x = x ◇ (y ◇ ((y ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxy_x_pxx_x_pxy_Equation646 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law646 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law646.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X1))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
  have eq23 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x (M.op (M.op x x) x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op (M.op X0 (M.op X0 X0)) X1) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq23 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq23 eq12
    | exact resolve eq12 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq37 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq37
    | exact resolve eq37 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq37
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
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
  have eq71 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq71 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq85 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq62
    | (have j0 := eq62 X0 X1
       grind)
    | exact resolve eq62 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq137 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq12
    | exact resolve eq12 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq76
    | (have j0 := eq76 (σ X0) (σ X1)
       grind)
    | exact resolve eq76 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X1) ∨ (M.op (M.op X0 (M.op X0 X0)) X1) = (k (M.op X0 (M.op X0 X0)) X1) ∨ (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq23 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq76 (M.op X0 (M.op X0 X0)) X1
       grind)
    | exact superpose eq76 eq23
    | (have j1 := eq76 (M.op X0 (M.op X0 X0)) X1
       grind)
    | exact resolve eq23 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq232 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq76 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq239 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq232 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq232 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq232 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq232 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq245 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) X1) = (k (M.op X0 (M.op X0 X0)) X1) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq215 X0 X1
       have j1 := eq32 X0 X1
       grind)
    | (have r₁ := eq215 X0 X1
       have r₂ := eq32 X0 X1
       grind)
    | exact resolve eq215 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq215
  have eq251 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq203 X0 X1
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq203
    | (have j0 := eq203 X0 X1
       grind)
    | exact resolve eq203 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq500 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq85 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq509 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq500 X0 X1
       have j1 := eq251 X0 X1
       grind)
    | (have r₁ := eq500 X0 X1
       have r₂ := eq251 X0 X1
       grind)
    | exact resolve eq500 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq500
  have eq1069 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq239 X0 (τ X1)
       grind)
    | exact superpose eq239 eq18
    | (have j1 := eq239 X0 (τ X1)
       grind)
    | exact resolve eq18 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq2934 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq509 x y
       grind)
    | exact superpose eq509 eq16
    | (have j1 := eq509 x y
       grind)
    | exact resolve eq16 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2985 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq509 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq46176 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1069 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1069
    | exact resolve eq1069 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069
  have eq46401 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq46176 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq46176
    | (have j0 := eq46176 X0 X1
       grind)
    | exact resolve eq46176 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46176
  have eq53827 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2934
       have i₂ := eq46401 y x
       grind)
    | exact superpose eq46401 eq2934
    | (have j1 := eq46401 (σ y) (σ x)
       grind)
    | (have r₁ := eq2934
       have r₂ := eq46401 y x
       grind)
    | exact resolve eq2934 eq46401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53828 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq53827
  have eq53844 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq53828
       grind)
    | exact superpose eq53828 eq16
    | exact resolve eq16 eq53828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53847 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq53828
       grind)
    | exact superpose eq53828 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq53828
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq53828
       grind)
    | exact resolve eq13 eq53828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53828
  have eq53895 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq53847
  have eq53900 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53895
       have i₂ := eq40 x
       grind)
    | exact superpose eq40 eq53895
    | exact resolve eq53895 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq53895
  have eq53905 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq53900
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq53900
    | exact resolve eq53900 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53900
  have eq881914 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq46401 y x
       have i₂ := eq53905
       grind)
    | exact superpose eq53905 eq46401
    | (have j0 := eq46401 y x
       grind)
    | exact resolve eq46401 eq53905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46401 eq53905
  have eq881921 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op x x)) := by grind
  clear eq881914
  have eq881930 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq881921
       have r₂ := eq53844
       grind)
    | exact resolve eq881921 eq53844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881921
  have eq882930 : (M.op x x) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq881930
       grind)
    | exact superpose eq881930 eq10
    | exact resolve eq10 eq881930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881930
  have eq883034 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq882930
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq882930
    | exact resolve eq882930 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq882930
  have eq884783 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq883034
       grind)
    | exact superpose eq883034 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq883034
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq883034
       grind)
    | exact resolve eq13 eq883034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq884855 : x ≠ x ∨ x = (M.op x x) ∨ x = (k x y) := by grind
  clear eq884783
  have eq884856 : x = (k x y) ∨ x = (M.op x x) := by grind
  clear eq884855
  have eq886496 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2985 x y
       have i₂ := eq884856
       grind)
    | exact superpose eq884856 eq2985
    | (have j0 := eq2985 x y
       grind)
    | exact resolve eq2985 eq884856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq884856
  have eq886524 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq886496
  have eq965052 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq886524
       grind)
    | exact superpose eq886524 eq16
    | exact resolve eq16 eq886524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886524
  have eq969760 : (σ x) ≠ (σ x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq965052
       have i₂ := eq883034
       grind)
    | exact superpose eq883034 eq965052
    | exact resolve eq965052 eq883034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883034 eq965052
  have eq969761 : (σ x) ≠ (σ x) ∨ x = (M.op x x) := by grind
  clear eq969760
  have eq969762 : x = (M.op x x) := by grind
  clear eq969761
  have eq971933 : ∀ X0 : G, (M.op X0 (M.op x x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 x X0
       have i₂ := eq969762
       grind)
    | exact superpose eq969762 eq23
    | exact resolve eq23 eq969762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq971951 : ∀ X0 : G, (k (M.op x x) X0) = (M.op (M.op x x) X0) ∨ (M.op x x) = (k (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq245 x x
       have i₂ := eq969762
       grind)
    | exact superpose eq969762 eq245
    | exact resolve eq245 eq969762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq972989 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ (M.op x x) = (k (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq971951 X0
       have i₂ := eq969762
       grind)
    | exact superpose eq969762 eq971951
    | (have j0 := eq971951 X0
       grind)
    | exact resolve eq971951 eq969762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971951
  have eq972995 : ∀ X0 : G, (M.op X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq971933 X0
       have i₂ := eq969762
       grind)
    | exact superpose eq969762 eq971933
    | exact resolve eq971933 eq969762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq971933
  have eq973321 : ∀ X0 : G, (M.op x X0) = (k x X0) ∨ x = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq972989 X0
       have i₂ := eq969762
       grind)
    | exact superpose eq969762 eq972989
    | (have j0 := eq972989 X0
       grind)
    | exact resolve eq972989 eq969762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969762 eq972989
  have eq1138240 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq2934
       have i₂ := eq973321 y
       grind)
    | exact superpose eq973321 eq2934
    | (have j1 := eq973321 y
       grind)
    | exact resolve eq2934 eq973321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2934 eq973321
  have eq1138326 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (k x y) := by grind
  clear eq1138240
  have eq1281462 : (σ x) ≠ (σ (M.op x x)) ∨ (k (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq137 x (σ y)
       have i₂ := eq1138326
       grind)
    | exact superpose eq1138326 eq137
    | (have j0 := eq137 x (σ y)
       grind)
    | exact resolve eq137 eq1138326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq1138326
  have eq1281495 : (σ x) ≠ (σ x) ∨ (k (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1281462
       have i₂ := eq972995 x
       grind)
    | exact superpose eq972995 eq1281462
    | exact resolve eq1281462 eq972995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281462
  have eq1281496 : (k (σ x) (σ y)) = (σ (M.op x x)) ∨ x = (k x y) := by grind
  clear eq1281495
  have eq1281508 : (σ x) = (k (σ x) (σ y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1281496
       have i₂ := eq972995 x
       grind)
    | exact superpose eq972995 eq1281496
    | exact resolve eq1281496 eq972995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972995 eq1281496
  have eq1281513 : (σ x) = (σ (k x y)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1281508
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1281508
    | exact resolve eq1281508 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281508
  have eq1293071 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1281513
       have i₂ := eq239 x y
       grind)
    | exact superpose eq239 eq1281513
    | (have j1 := eq239 x y
       grind)
    | exact resolve eq1281513 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq1293078 : (k x y) = (τ (σ x)) ∨ x = (k x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq1281513
       grind)
    | exact superpose eq1281513 eq10
    | exact resolve eq10 eq1281513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1281513
  have eq1293125 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq1293071
  have eq1293145 : x = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1293078
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1293078
    | exact resolve eq1293078 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293078
  have eq1293146 : x = (k x y) := by grind
  clear eq1293145
  have eq1293151 : x = (M.op x y) := by
    first
    | (have r₁ := eq1293125
       have r₂ := eq53844
       grind)
    | exact resolve eq1293125 eq53844
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53844 eq1293125
  have eq1299646 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2985 x y
       have i₂ := eq1293146
       grind)
    | exact superpose eq1293146 eq2985
    | (have j0 := eq2985 x y
       grind)
    | exact resolve eq2985 eq1293146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2985 eq1293146
  have eq1299673 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq1299646
  have eq1313742 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1299673
       grind)
    | exact superpose eq1299673 eq16
    | exact resolve eq16 eq1299673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1299673
  have eq1313837 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq1313742
       have i₂ := eq1293151
       grind)
    | exact superpose eq1293151 eq1313742
    | exact resolve eq1313742 eq1293151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1293151 eq1313742
  have eq1313838 : False := by grind
  exact eq1313838

/-- `Equation646`: `x = x ◇ (y ◇ ((y ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(X,X) = X then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxx_x_pxx_pxx_pyx_Equation646 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law646 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law646.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X1))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq23 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x (M.op (M.op x x) x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X1 (M.op X0 (M.op X0 X0))) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq23 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq23 eq12
    | (have r₁ := eq12 (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))
       have r₂ := eq23 X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))
       grind)
    | exact resolve eq12 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq32
    | (have j0 := eq32 X0 X1
       grind)
    | (have r₁ := eq32 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq23 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq32 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq43 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq43
    | exact resolve eq43 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq43
  have eq50 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X0 (M.op X0 X0))) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq23 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq23 eq13
    | (have r₁ := eq13 (M.op X0 (M.op X0 X0)) X1
       have r₂ := eq23 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq13 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X0 (M.op X0 X0))) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq53 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = X1 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq55 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 (k (M.op X0 (M.op X0 X0)) X1)
       have j1 := eq38 X0 X1
       grind)
    | (have r₁ := eq53 X0 X1
       have r₂ := eq38 X0 X1
       grind)
    | (have r₁ := eq53 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq38 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq53 X0 X1
       have r₂ := eq38 X0 (k (M.op X0 (M.op X0 X0)) X1)
       grind)
    | exact resolve eq53 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq53
  have eq72 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq82 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
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
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq92 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq46 X1
       grind)
    | exact superpose eq46 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 X1
       have i₂ := eq46 X1
       grind)
    | exact superpose eq46 eq92
    | (have j0 := eq92 X0 X1
       grind)
    | exact resolve eq92 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq132 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) X1
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq23
    | exact resolve eq23 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq161 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq87
    | (have j0 := eq87 (σ X0) X1
       grind)
    | exact resolve eq87 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq194 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq188 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq188 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq188 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq188 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq203 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq161 X0 X1
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq161
    | (have j0 := eq161 X0 X1
       grind)
    | exact resolve eq161 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq161
  have eq211 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq203 X0 X1
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq203
    | (have j0 := eq203 X0 X1
       grind)
    | exact resolve eq203 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq407 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq132 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq23 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq23 eq132
    | exact resolve eq132 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq444 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq407 X0 X1
       have i₂ := eq46 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq46 eq407
    | exact resolve eq407 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq407
  have eq455 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq444 X0 X1
       have i₂ := eq23 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq23 eq444
    | exact resolve eq444 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq1004 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq1008 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1004 X0 X1
       have j1 := eq211 X1 X0
       grind)
    | (have r₁ := eq1004 X1 X0
       have r₂ := eq211 X0 X1
       grind)
    | exact resolve eq1004 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211 eq1004
  have eq1171 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq194 X1 (τ X0)
       grind)
    | exact superpose eq194 eq18
    | (have j1 := eq194 X1 X1
       grind)
    | exact resolve eq18 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1179 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq194 X0 X2
       grind)
    | exact superpose eq194 eq23
    | (have j1 := eq194 X0 X2
       grind)
    | exact resolve eq23 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq2581 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq1008 X1 X0
       grind)
    | exact superpose eq1008 eq10
    | (have j1 := eq1008 X1 X0
       grind)
    | exact resolve eq10 eq1008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1008
  have eq2616 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2581 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2581
    | (have j0 := eq2581 X0 X1
       grind)
    | exact resolve eq2581 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2581
  have eq7988 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq455 X0 X1
       have i₂ := eq1179 X0 X0 X2
       grind)
    | exact superpose eq1179 eq455
    | (have j1 := eq1179 X0 X1 X2
       grind)
    | exact resolve eq455 eq1179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq455 eq1179
  have eq8918 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq7988 y (σ x) X0
       grind)
    | exact superpose eq7988 eq16
    | (have j1 := eq7988 y x X0
       grind)
    | exact resolve eq16 eq7988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7988
  have eq31959 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1171 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1171
    | (have j0 := eq1171 X0 X1
       grind)
    | exact resolve eq1171 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1171
  have eq32399 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31959 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq31959
    | (have j0 := eq31959 X0 X1
       grind)
    | exact resolve eq31959 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31959
  have eq33062 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2616 y x
       grind)
    | exact superpose eq2616 eq16
    | (have j1 := eq2616 y x
       grind)
    | exact resolve eq16 eq2616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2616
  have eq33269 : y = (M.op y y) := by
    first
    | (have j1 := eq32399 x y
       grind)
    | (have r₁ := eq33062
       have r₂ := eq32399 x y
       grind)
    | exact resolve eq33062 eq32399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32399 eq33062
  have eq33428 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 y X0
       have i₂ := eq33269
       grind)
    | exact superpose eq33269 eq23
    | exact resolve eq23 eq33269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq33431 : ∀ X0 : G, (M.op y y) = (k (M.op y y) X0) := by
    intro X0
    first
    | (have i₁ := eq55 y x
       have i₂ := eq33269
       grind)
    | exact superpose eq33269 eq55
    | exact resolve eq55 eq33269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq33522 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq33431 X0
       have i₂ := eq33269
       grind)
    | exact superpose eq33269 eq33431
    | exact resolve eq33431 eq33269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33431
  have eq33525 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq33428 X0
       have i₂ := eq33269
       grind)
    | exact superpose eq33269 eq33428
    | exact resolve eq33428 eq33269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33269 eq33428
  have eq34325 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq8918 X0
       have i₂ := eq33525 x
       grind)
    | exact superpose eq33525 eq8918
    | (have j0 := eq8918 X0
       grind)
    | exact resolve eq8918 eq33525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8918
  have eq34326 : ∀ X0 : G, (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq34325 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34325
  have eq34329 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq34326 X0
       have i₂ := eq33522 X0
       grind)
    | exact superpose eq33522 eq34326
    | exact resolve eq34326 eq33522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33522 eq34326
  have eq34744 : ∀ X0 : G, y = X0 := by
    intro X0
    first
    | (have i₁ := eq33525 X0
       have i₂ := eq34329 X0
       grind)
    | exact superpose eq34329 eq33525
    | exact resolve eq33525 eq34329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33525 eq34329
  have eq35307 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34744 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq34744 eq16
    | exact resolve eq16 eq34744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35908 : False := by grind
  exact eq35908

/-- `Equation646`: `x = x ◇ (y ◇ ((y ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(X,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxx_x_pxx_x_pyx_Equation646 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law646 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law646.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X1))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq23 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x (M.op (M.op x x) x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X1 (M.op X0 (M.op X0 X0))) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq23 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq23 eq12
    | (have r₁ := eq12 (M.op X0 (M.op X0 X0)) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))
       have r₂ := eq23 X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))
       grind)
    | exact resolve eq12 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq32 X0 X1
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq32
    | (have j0 := eq32 X0 X1
       grind)
    | (have r₁ := eq32 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq23 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq32 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq43 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq35 (σ X0)
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq43 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq43
    | exact resolve eq43 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq43
  have eq50 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X0 (M.op X0 X0))) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq23 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq23 eq13
    | (have j0 := eq13 (M.op X0 (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq13 (M.op X0 (M.op X0 X0)) X1
       have r₂ := eq23 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact resolve eq13 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op X0 (M.op X0 X0))) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq53 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = X1 ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq23 X0 X1
       grind)
    | exact superpose eq23 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq55 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 (k (M.op X0 (M.op X0 X0)) X1)
       have j1 := eq38 X0 X1
       grind)
    | (have r₁ := eq53 X0 X1
       have r₂ := eq38 X0 X1
       grind)
    | (have r₁ := eq53 X0 (M.op X0 (M.op X0 X0))
       have r₂ := eq38 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq53 X0 X1
       have r₂ := eq38 X0 (k (M.op X0 (M.op X0 X0)) X1)
       grind)
    | exact resolve eq53 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq53
  have eq72 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq82 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
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
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq82 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq92 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq46 X1
       grind)
    | exact superpose eq46 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq95 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92 X0 X1
       have i₂ := eq46 X1
       grind)
    | exact superpose eq46 eq92
    | (have j0 := eq92 X0 X1
       grind)
    | exact resolve eq92 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq132 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) X1
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq23
    | exact resolve eq23 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq160 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq87 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq87
    | (have j0 := eq87 (σ X0) X1
       grind)
    | exact resolve eq87 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq193 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq187 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq187 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq187 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq187 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq202 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq160 X0 X1
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq160
    | (have j0 := eq160 X0 X1
       grind)
    | exact resolve eq160 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq208 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (σ (M.op X0 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq202 X0 X1
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq202
    | (have j0 := eq202 X0 X1
       grind)
    | exact resolve eq202 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq402 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq132 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq23 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq23 eq132
    | exact resolve eq132 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq439 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq402 X0 X1
       have i₂ := eq46 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq46 eq402
    | exact resolve eq402 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq402
  have eq450 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq439 X0 X1
       have i₂ := eq23 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq23 eq439
    | exact resolve eq439 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq999 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq95 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq1003 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq999 X0 X1
       have j1 := eq208 X1 X0
       grind)
    | (have r₁ := eq999 X1 X0
       have r₂ := eq208 X0 X1
       grind)
    | exact resolve eq999 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq999
  have eq1166 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq193 X1 (τ X0)
       grind)
    | exact superpose eq193 eq18
    | (have j1 := eq193 X1 X1
       grind)
    | exact resolve eq18 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1174 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq193 X0 X2
       grind)
    | exact superpose eq193 eq23
    | (have j1 := eq193 X0 X2
       grind)
    | exact resolve eq23 eq193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq193
  have eq2575 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq1003 X1 X0
       grind)
    | exact superpose eq1003 eq10
    | (have j1 := eq1003 X1 X0
       grind)
    | exact resolve eq10 eq1003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq2610 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq2575 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2575
    | (have j0 := eq2575 X0 X1
       grind)
    | exact resolve eq2575 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2575
  have eq7896 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq450 X0 X1
       have i₂ := eq1174 X0 X0 X2
       grind)
    | exact superpose eq1174 eq450
    | (have j1 := eq1174 X0 X1 X2
       grind)
    | exact resolve eq450 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450 eq1174
  have eq8821 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq7896 y (σ x) X0
       grind)
    | exact superpose eq7896 eq16
    | (have j1 := eq7896 y x X0
       grind)
    | exact resolve eq16 eq7896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7896
  have eq31799 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1166 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1166
    | (have j0 := eq1166 X0 X1
       grind)
    | exact resolve eq1166 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166
  have eq32239 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq31799 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq31799
    | (have j0 := eq31799 X0 X1
       grind)
    | exact resolve eq31799 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31799
  have eq32898 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2610 y x
       grind)
    | exact superpose eq2610 eq16
    | (have j1 := eq2610 y x
       grind)
    | exact resolve eq16 eq2610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2610
  have eq33105 : y = (M.op y y) := by
    first
    | (have j1 := eq32239 x y
       grind)
    | (have r₁ := eq32898
       have r₂ := eq32239 x y
       grind)
    | exact resolve eq32898 eq32239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32239 eq32898
  have eq33260 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq23 y X0
       have i₂ := eq33105
       grind)
    | exact superpose eq33105 eq23
    | exact resolve eq23 eq33105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq33263 : ∀ X0 : G, (M.op y y) = (k (M.op y y) X0) := by
    intro X0
    first
    | (have i₁ := eq55 y x
       have i₂ := eq33105
       grind)
    | exact superpose eq33105 eq55
    | exact resolve eq55 eq33105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq33354 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq33263 X0
       have i₂ := eq33105
       grind)
    | exact superpose eq33105 eq33263
    | exact resolve eq33263 eq33105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33263
  have eq33357 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq33260 X0
       have i₂ := eq33105
       grind)
    | exact superpose eq33105 eq33260
    | exact resolve eq33260 eq33105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33105 eq33260
  have eq34270 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq8821 X0
       have i₂ := eq33357 x
       grind)
    | exact superpose eq33357 eq8821
    | (have j0 := eq8821 X0
       grind)
    | exact resolve eq8821 eq33357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8821
  have eq34271 : ∀ X0 : G, (M.op X0 y) = (k y X0) := by
    intro X0
    first
    | (have j0 := eq34270 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34270
  have eq34273 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq34271 X0
       have i₂ := eq33354 X0
       grind)
    | exact superpose eq33354 eq34271
    | exact resolve eq34271 eq33354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33354 eq34271
  have eq34375 : ∀ X0 : G, y = X0 := by
    intro X0
    first
    | (have i₁ := eq33357 X0
       have i₂ := eq34273 X0
       grind)
    | exact superpose eq34273 eq33357
    | exact resolve eq33357 eq34273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33357 eq34273
  have eq35258 : y ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34375 (M.op (σ x) (σ y))
       grind)
    | exact superpose eq34375 eq16
    | exact resolve eq16 eq34375
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35860 : False := by grind
  exact eq35860

/-- `Equation646`: `x = x ◇ (y ◇ ((y ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then X else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pxx_pyx_x_pxx_pyx_Equation646 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law646 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law646.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X1))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq19 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x (M.op (M.op x x) x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq51 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq57 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq74 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq33 (σ X0)
       grind)
    | exact superpose eq33 eq15
    | (have j1 := eq33 (σ X0)
       grind)
    | exact resolve eq15 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq173 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq179 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq173 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq173 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq173 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq173 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq196 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq179 X1 (τ X0)
       grind)
    | exact superpose eq179 eq18
    | (have j1 := eq179 X1 X1
       grind)
    | exact resolve eq18 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq203 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq179 X0 X2
       grind)
    | exact superpose eq179 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq179 X0 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq179 X0 X1
       grind)
    | exact resolve eq12 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq206 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq203 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq285 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ X0) X1) ∨ (M.op X2 X0) = (k X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37 X0 X1
       have i₂ := eq206 X0 (σ X1) X2
       grind)
    | exact superpose eq206 eq37
    | (have j1 := eq206 (τ X0) X1 X2
       grind)
    | exact resolve eq37 eq206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq206
  have eq845 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (τ (σ X1)) = (k (τ (σ X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq285 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq285 eq15
    | (have j1 := eq285 (σ X1) X2 X2
       grind)
    | exact resolve eq15 eq285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq855 : ∀ X0 X1 X2 : G, (k X1 X2) = X1 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq845 X0 X0 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq845
    | (have j0 := eq845 X0 X1 X2
       grind)
    | exact resolve eq845 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq1989 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq74 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq4036 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq196 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq196
    | (have j0 := eq196 X0 X1
       grind)
    | exact resolve eq196 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq4149 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4036 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4036
    | (have j0 := eq4036 X0 X1
       grind)
    | exact resolve eq4036 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4036
  have eq4464 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq4149 X2 X0
       grind)
    | exact superpose eq4149 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq4149 X2 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq4149 X0 X1
       grind)
    | exact resolve eq12 eq4149
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4149
  have eq4478 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (σ (k X0 X2)) = (σ (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq4464 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4464
  have eq6057 : ∀ X0 : G, (σ (τ X0)) ≠ (k (σ (τ X0)) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1989 (τ X0)
       have i₂ := eq18 X0 (τ X0)
       grind)
    | exact superpose eq18 eq1989
    | (have j0 := eq1989 (τ X0)
       grind)
    | exact resolve eq1989 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq6081 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq6057 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6057
    | (have j0 := eq6057 X0
       grind)
    | exact resolve eq6057 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6057
  have eq6089 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq6081 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq6081
    | (have j0 := eq6081 X0
       grind)
    | exact resolve eq6081 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6081
  have eq13472 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq855 x y X0
       grind)
    | exact superpose eq855 eq16
    | (have j1 := eq855 X0 y X0
       grind)
    | exact resolve eq16 eq855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq855
  have eq13565 : ∀ X0 : G, y = (k y X0) := by
    intro X0
    first
    | (have j0 := eq13472 X0
       have j1 := eq4478 y X0 x
       grind)
    | (have r₁ := eq13472 X0
       have r₂ := eq4478 y x x
       grind)
    | exact resolve eq13472 eq4478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4478 eq13472
  have eq13712 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1989 y
       have i₂ := eq13565 y
       grind)
    | exact superpose eq13565 eq1989
    | (have j0 := eq1989 y
       grind)
    | exact resolve eq1989 eq13565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1989
  have eq13714 : y ≠ y ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq6089 y
       have i₂ := eq13565 y
       grind)
    | exact superpose eq13565 eq6089
    | (have j0 := eq6089 y
       grind)
    | (have r₁ := eq6089 y
       have r₂ := eq13565 y
       grind)
    | exact resolve eq6089 eq13565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6089 eq13565
  have eq13767 : y = (M.op y y) := by grind
  clear eq13714
  have eq13768 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq13712
  have eq14023 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq19 y X0
       have i₂ := eq13767
       grind)
    | exact superpose eq13767 eq19
    | exact resolve eq19 eq13767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14051 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq14023 X0
       have i₂ := eq13767
       grind)
    | exact superpose eq13767 eq14023
    | exact resolve eq14023 eq13767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13767 eq14023
  have eq15361 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq19 (σ y) X0
       have i₂ := eq13768
       grind)
    | exact superpose eq13768 eq19
    | exact resolve eq19 eq13768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq15390 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq15361 X0
       have i₂ := eq13768
       grind)
    | exact superpose eq13768 eq15361
    | exact resolve eq15361 eq13768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13768 eq15361
  have eq15915 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15390 (σ x)
       grind)
    | exact superpose eq15390 eq16
    | exact resolve eq16 eq15390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15390
  have eq15928 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq15915
       have i₂ := eq14051 x
       grind)
    | exact superpose eq14051 eq15915
    | exact resolve eq15915 eq14051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14051 eq15915
  have eq15929 : False := by grind
  exact eq15929

/-- `Equation646`: `x = x ◇ (y ◇ ((y ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_pxx_pxy_Equation646 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law646 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law646.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X1))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq23 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x (M.op (M.op x x) x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X1) X0)) ≠ (M.op X0 (M.op (M.op X0 X1) X0)) ∨ (M.op X2 X2) = X2 ∨ (M.op X2 X2) = (k X2 (M.op X0 (M.op (M.op X0 X1) X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 (M.op (M.op X0 X1) X0))
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X1) X0)) X0 X1
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X2 (M.op X0 (M.op (M.op X0 X1) X0))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op (M.op X1 X2) X1))
       have r₂ := eq9 (M.op X1 (M.op (M.op X1 X2) X1)) X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (k X2 (M.op X0 (M.op (M.op X0 X1) X0))) ∨ (M.op X2 X2) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq62 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 X2 X2
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq62 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq72 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq63 X0 (M.op X0 X0) X2
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq63 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq63 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq73 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq68 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq68 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq68 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq101 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq73 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq101 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq105 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq102 (σ X0)
       grind)
    | exact superpose eq102 eq15
    | exact resolve eq15 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq105 X0
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq105
    | exact resolve eq105 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq144 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X1))) = (M.op X0 X0) ∨ (k X3 X0) = (M.op X3 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq73 X0 (M.op X1 (M.op (M.op X1 X2) X1)) X3
       have i₂ := eq46 X1 X2 X0
       grind)
    | exact superpose eq46 eq73
    | (have j0 := eq73 X3 X0 X2
       have j1 := eq46 X0 X1 X0
       grind)
    | exact resolve eq73 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq73
  have eq149 : ∀ X0 X3 : G, (M.op X0 X0) = X0 ∨ (k X3 X0) = (M.op X3 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X3
    first
    | (have i₁ := eq144 X0 x x X3
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq144
    | (have j0 := eq144 X0 x x X3
       grind)
    | exact resolve eq144 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144
  have eq150 : ∀ X0 X3 : G, (M.op X0 X0) = X0 ∨ (k X3 X0) = (M.op X3 X0) := by
    intro X0 X3
    first
    | (have j0 := eq149 X0 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149
  have eq175 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq102 (τ X0)
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq102
    | exact resolve eq102 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq179 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq175 X0
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq175
    | exact resolve eq175 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq175
  have eq208 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) X1
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq23
    | exact resolve eq23 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 X1 : G, (M.op X1 (M.op (τ X0) (τ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (τ X0) X1
       have i₂ := eq179 X0
       grind)
    | exact superpose eq179 eq23
    | exact resolve eq23 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq427 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq208 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq23 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq23 eq208
    | exact resolve eq208 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq464 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq427 X0 X1
       have i₂ := eq114 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq114 eq427
    | exact resolve eq427 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427
  have eq474 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq464 X0 X1
       have i₂ := eq23 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq23 eq464
    | exact resolve eq464 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq464
  have eq798 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op (σ X0) (σ (M.op X0 X0)))) (τ (M.op (σ X0) (σ (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq370 (M.op (σ X0) (σ (M.op X0 X0))) X1
       have i₂ := eq208 X0 (M.op (σ X0) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq208 eq370
    | exact resolve eq370 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq848 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (M.op (σ X0) (σ (M.op X0 X0))) (M.op (σ X0) (σ (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq798 X0 X1
       have i₂ := eq179 (M.op (σ X0) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq179 eq798
    | exact resolve eq798 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq798
  have eq862 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (σ X0) (σ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq848 X0 X1
       have i₂ := eq208 X0 (M.op (σ X0) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq208 eq848
    | exact resolve eq848 eq208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq848
  have eq903 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq150 (σ X1) (σ X0)
       grind)
    | exact superpose eq150 eq15
    | (have j1 := eq150 (σ X1) x
       grind)
    | exact resolve eq15 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq911 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq903 X0 X1
       have i₂ := eq114 X1
       grind)
    | exact superpose eq114 eq903
    | (have j0 := eq903 X0 X1
       grind)
    | exact resolve eq903 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq903
  have eq1020 : ∀ X0 X1 X2 : G, (M.op X1 (σ X0)) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq474 X0 X1
       have i₂ := eq72 X0 X0 X2
       grind)
    | exact superpose eq72 eq474
    | (have j1 := eq72 X0 X1 X2
       grind)
    | exact resolve eq474 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq474
  have eq4036 : ∀ X0 X1 X2 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X2 (σ (τ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq1020 (τ X1) X2 X0
       grind)
    | exact superpose eq1020 eq18
    | (have j1 := eq1020 (τ X1) X2 X2
       grind)
    | exact resolve eq18 eq1020
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1020
  have eq4050 : ∀ X0 X1 X2 : G, (M.op X2 X1) = X2 ∨ (k (σ X0) X1) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4036 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq4036
    | (have j0 := eq4036 X0 X1 X2
       grind)
    | exact resolve eq4036 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4036
  have eq61608 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 (τ (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq114 X0
       have i₂ := eq4050 X1 (σ X0) (σ X0)
       grind)
    | exact superpose eq4050 eq114
    | (have j1 := eq4050 X1 (σ X0) x
       grind)
    | exact resolve eq114 eq4050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4050
  have eq61898 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61608 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq61608
    | (have j0 := eq61608 X0 X1
       grind)
    | exact resolve eq61608 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61608
  have eq62066 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61898 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq61898
    | (have j0 := eq61898 X0 X1
       grind)
    | exact resolve eq61898 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61898
  have eq62535 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq911 x y
       grind)
    | exact superpose eq911 eq16
    | (have j1 := eq911 x y
       grind)
    | exact resolve eq16 eq911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq911
  have eq62839 : (σ y) = (σ (M.op y y)) := by
    first
    | (have j1 := eq62066 y x
       grind)
    | (have r₁ := eq62535
       have r₂ := eq62066 y x
       grind)
    | exact resolve eq62535 eq62066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62066 eq62535
  have eq63124 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq208 y X0
       have i₂ := eq62839
       grind)
    | exact superpose eq62839 eq208
    | exact resolve eq208 eq62839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208
  have eq63130 : ∀ X0 : G, (M.op X0 (τ (M.op (σ y) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq862 y X0
       have i₂ := eq62839
       grind)
    | exact superpose eq62839 eq862
    | exact resolve eq862 eq62839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862
  have eq63141 : (τ (σ y)) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq62839
       grind)
    | exact superpose eq62839 eq10
    | exact resolve eq10 eq62839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63238 : y = (M.op y y) := by
    first
    | (have i₁ := eq63141
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq63141
    | exact resolve eq63141 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63141
  have eq63247 : ∀ X0 : G, (M.op X0 (τ (σ (M.op y y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq63130 X0
       have i₂ := eq114 y
       grind)
    | exact superpose eq114 eq63130
    | exact resolve eq63130 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63130
  have eq63250 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq63124 X0
       have i₂ := eq114 y
       grind)
    | exact superpose eq114 eq63124
    | exact resolve eq63124 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq63124
  have eq63261 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq63247 X0
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq63247
    | exact resolve eq63247 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63247
  have eq63264 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq63250 X0
       have i₂ := eq62839
       grind)
    | exact superpose eq62839 eq63250
    | exact resolve eq63250 eq62839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62839 eq63250
  have eq63272 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq63261 X0
       have i₂ := eq63238
       grind)
    | exact superpose eq63238 eq63261
    | exact resolve eq63261 eq63238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63238 eq63261
  have eq67221 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq63264 (σ x)
       grind)
    | exact superpose eq63264 eq16
    | exact resolve eq16 eq63264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63264
  have eq67255 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq67221
       have i₂ := eq63272 x
       grind)
    | exact superpose eq63272 eq67221
    | exact resolve eq67221 eq63272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63272 eq67221
  have eq67256 : False := by grind
  exact eq67256

/-- `Equation646`: `x = x ◇ (y ◇ ((y ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pxy_x_pxy_Equation646 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law646 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law646.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X1))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq23 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x (M.op (M.op x x) x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X0 X1) X0)) ≠ (M.op X0 (M.op (M.op X0 X1) X0)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (M.op X0 (M.op (M.op X0 X1) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 (M.op (M.op X0 X1) X0))
       have i₂ := eq9 (M.op X0 (M.op (M.op X0 X1) X0)) X0 X1
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X2 (M.op X0 (M.op (M.op X0 X1) X0))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op (M.op X1 X2) X1))
       have r₂ := eq9 (M.op X1 (M.op (M.op X1 X2) X1)) X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 X1 X2 : G, (M.op X2 X2) = X2 ∨ (k X2 (M.op X0 (M.op (M.op X0 X1) X0))) = X2 := by
    intro X0 X1 X2
    first
    | (have j0 := eq43 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq47 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq61 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X2
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq23
    | (have j1 := eq14 X2 X2
       grind)
    | exact resolve eq23 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq62 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq69 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq61 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq72 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq63 X0 X1 X2
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq63 X0 (M.op X0 X0) X2
       have r₂ := eq12 (M.op X0 X0) X1
       grind)
    | (have r₁ := eq63 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq63 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq73 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq68 X0 X1 X2
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq68 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq68 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq74 : ∀ X0 X1 X2 : G, (M.op X1 X1) = X1 ∨ (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq69 X0 X1 X1
       have j1 := eq12 X2 X0
       grind)
    | (have r₁ := eq69 X0 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq69 X0 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq69 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq101 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq73 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq102 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq101 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq105 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq102 (σ X0)
       grind)
    | exact superpose eq102 eq15
    | exact resolve eq15 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq105 X0
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq105
    | exact resolve eq105 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq135 : ∀ X0 X1 X2 X3 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 (M.op X2 (M.op (M.op X2 X3) X2))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq46 X2 X3 X0
       grind)
    | exact superpose eq46 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq46 X2 X3 X0
       grind)
    | (have r₁ := eq12 X2 X1
       have r₂ := eq46 X0 X1 X2
       grind)
    | exact resolve eq12 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq145 : ∀ X0 X1 X2 X3 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 (M.op X2 (M.op (M.op X2 X3) X2))) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq135 X0 X1 X2 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq164 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq102 (τ X0)
       have i₂ := eq47 X0 X0
       grind)
    | exact superpose eq47 eq102
    | exact resolve eq102 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq168 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq164 X0
       have i₂ := eq102 X0
       grind)
    | exact superpose eq102 eq164
    | exact resolve eq164 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164
  have eq198 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X2) = X2 ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq74 (σ X1) X2 (σ X0)
       grind)
    | exact superpose eq74 eq15
    | (have j1 := eq74 (σ X1) X2 X2
       grind)
    | exact resolve eq15 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq233 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (σ X0) X1
       have i₂ := eq114 X0
       grind)
    | exact superpose eq114 eq23
    | exact resolve eq23 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 X1 : G, (M.op X1 (M.op (τ X0) (τ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq23 (τ X0) X1
       have i₂ := eq168 X0
       grind)
    | exact superpose eq168 eq23
    | exact resolve eq23 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq713 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op X0 (M.op X0 X0))) (τ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq337 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq23 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq23 eq337
    | exact resolve eq337 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq715 : ∀ X0 X1 : G, (M.op X1 (M.op (τ (M.op (σ X0) (σ (M.op X0 X0)))) (τ (M.op (σ X0) (σ (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq337 (M.op (σ X0) (σ (M.op X0 X0))) X1
       have i₂ := eq233 X0 (M.op (σ X0) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq233 eq337
    | exact resolve eq337 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq762 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (M.op (σ X0) (σ (M.op X0 X0))) (M.op (σ X0) (σ (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq715 X0 X1
       have i₂ := eq168 (M.op (σ X0) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq168 eq715
    | exact resolve eq715 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq764 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq713 X0 X1
       have i₂ := eq168 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq168 eq713
    | exact resolve eq713 eq168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168 eq713
  have eq776 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (σ X0) (σ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq762 X0 X1
       have i₂ := eq233 X0 (M.op (σ X0) (σ (M.op X0 X0)))
       grind)
    | exact superpose eq233 eq762
    | exact resolve eq762 eq233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq778 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq764 X0 X1
       have i₂ := eq23 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq23 eq764
    | exact resolve eq764 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq885 : ∀ X0 X1 : G, (M.op X1 (τ (M.op (τ (M.op X0 (M.op X0 X0))) (τ (M.op X0 (M.op X0 X0)))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq778 (τ (M.op X0 (M.op X0 X0))) X1
       have i₂ := eq778 X0 (τ (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq778 eq778
    | exact resolve eq778 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq923 : ∀ X0 X1 : G, (M.op X1 (τ (τ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq885 X0 X1
       have i₂ := eq778 X0 (τ (M.op X0 (M.op X0 X0)))
       grind)
    | exact superpose eq778 eq885
    | exact resolve eq885 eq778
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq778 eq885
  have eq969 : ∀ X0 X1 X2 : G, (M.op X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X0 X1
       have i₂ := eq72 X0 X0 X2
       grind)
    | exact superpose eq72 eq23
    | (have j1 := eq72 X0 X1 X2
       grind)
    | exact resolve eq23 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq1476 : ∀ X0 X1 X2 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq969 X1 X2 (τ X0)
       grind)
    | exact superpose eq969 eq17
    | (have j1 := eq969 X1 X2 X2
       grind)
    | exact resolve eq17 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq3221 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X1))) ≠ X0 ∨ (k X0 (M.op X1 (M.op (M.op X1 X2) X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq145 X0 X1 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145
  have eq3222 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op (M.op X1 X2) X1))) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq3221 X0 X1 X2
       grind)
    | (have r₁ := eq3221 X0 X1 X2
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq3221 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3221
  have eq3257 : ∀ X0 X1 : G, (k X1 (M.op X0 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3222 X1 X0 (τ (τ (M.op x (M.op x x))))
       have i₂ := eq923 x X0
       grind)
    | exact superpose eq923 eq3222
    | exact resolve eq3222 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923 eq3222
  have eq3545 : ∀ X0 X1 X2 : G, (k X1 X0) = X1 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3257 X0 X1
       have i₂ := eq72 X0 X0 X2
       grind)
    | exact superpose eq72 eq3257
    | (have j1 := eq72 X0 X1 X2
       grind)
    | exact resolve eq3257 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq3257
  have eq6989 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq3545 X1 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3545
  have eq7489 : ∀ X0 X1 X2 : G, (τ X0) = (k (τ X0) X1) ∨ (σ (k X2 X1)) = (M.op (σ X2) (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq198 X2 X1 X0
       grind)
    | exact superpose eq198 eq22
    | (have j1 := eq198 X2 X1 X0
       grind)
    | exact resolve eq22 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq198
  have eq115850 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1476 (σ X0) X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1476
    | (have j0 := eq1476 X0 X1 X2
       grind)
    | exact resolve eq1476 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1476
  have eq116934 : ∀ X0 X1 X2 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X2 X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq115850 X0 X1 X2
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq115850
    | (have j0 := eq115850 X0 X1 X2
       grind)
    | exact resolve eq115850 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115850
  have eq118558 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = X0 ∨ (σ (k X2 X1)) = (σ (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6989 X0 X1
       have i₂ := eq116934 X2 X1 X0
       grind)
    | exact superpose eq116934 eq6989
    | (have j0 := eq6989 X0 X1
       have j1 := eq116934 X2 X1 X2
       grind)
    | (have r₁ := eq6989 X2 X1
       have r₂ := eq116934 X0 X1 X2
       grind)
    | exact resolve eq6989 eq116934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6989 eq116934
  have eq118846 : ∀ X0 X1 X2 : G, (k X0 X1) = X0 ∨ (σ (k X2 X1)) = (σ (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq118558 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118558
  have eq207861 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k x y)) ∨ (τ X0) = (k (τ X0) y) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq7489 X0 y x
       grind)
    | exact superpose eq7489 eq16
    | (have j1 := eq7489 X0 y x
       grind)
    | exact resolve eq16 eq7489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7489
  have eq208696 : ∀ X0 : G, (τ X0) = (k (τ X0) y) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq207861 X0
       have j1 := eq118846 (τ X0) y x
       grind)
    | (have r₁ := eq207861 X0
       have r₂ := eq118846 X0 y x
       grind)
    | exact resolve eq207861 eq118846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118846 eq207861
  have eq209076 : ∀ X0 : G, (σ (τ X0)) = (k X0 (σ y)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq17 X0 y
       have i₂ := eq208696 X0
       grind)
    | exact superpose eq208696 eq17
    | (have j1 := eq208696 X0
       grind)
    | exact resolve eq17 eq208696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq208696
  have eq209614 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq209076 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq209076
    | (have j0 := eq209076 X0
       grind)
    | exact resolve eq209076 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209076
  have eq211769 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq102 (σ y)
       have i₂ := eq209614 (σ y)
       grind)
    | exact superpose eq209614 eq102
    | (have j1 := eq209614 (σ y)
       grind)
    | exact resolve eq102 eq209614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq209614
  have eq212179 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq211769
  have eq212363 : (σ y) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq212179
       have i₂ := eq114 y
       grind)
    | exact superpose eq114 eq212179
    | exact resolve eq212179 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212179
  have eq214187 : ∀ X0 : G, (M.op X0 (M.op (σ y) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq233 y X0
       have i₂ := eq212363
       grind)
    | exact superpose eq212363 eq233
    | exact resolve eq233 eq212363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq214193 : ∀ X0 : G, (M.op X0 (τ (M.op (σ y) (σ y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq776 y X0
       have i₂ := eq212363
       grind)
    | exact superpose eq212363 eq776
    | exact resolve eq776 eq212363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776
  have eq214223 : (M.op y y) = (τ (σ y)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq212363
       grind)
    | exact superpose eq212363 eq10
    | exact resolve eq10 eq212363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214427 : y = (M.op y y) := by
    first
    | (have i₁ := eq214223
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq214223
    | exact resolve eq214223 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214223
  have eq214449 : ∀ X0 : G, (M.op X0 (τ (σ (M.op y y)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq214193 X0
       have i₂ := eq114 y
       grind)
    | exact superpose eq114 eq214193
    | exact resolve eq214193 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214193
  have eq214452 : ∀ X0 : G, (M.op X0 (σ (M.op y y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq214187 X0
       have i₂ := eq114 y
       grind)
    | exact superpose eq114 eq214187
    | exact resolve eq214187 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq214187
  have eq214479 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq214449 X0
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq214449
    | exact resolve eq214449 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214449
  have eq214482 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq214452 X0
       have i₂ := eq212363
       grind)
    | exact superpose eq212363 eq214452
    | exact resolve eq214452 eq212363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212363 eq214452
  have eq214500 : ∀ X0 : G, (M.op X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq214479 X0
       have i₂ := eq214427
       grind)
    | exact superpose eq214427 eq214479
    | exact resolve eq214479 eq214427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214427 eq214479
  have eq221988 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq214482 (σ x)
       grind)
    | exact superpose eq214482 eq16
    | exact resolve eq16 eq214482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214482
  have eq222047 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq221988
       have i₂ := eq214500 x
       grind)
    | exact superpose eq214500 eq221988
    | exact resolve eq221988 eq214500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214500 eq221988
  have eq222048 : False := by grind
  exact eq222048

/-- `Equation646`: `x = x ◇ (y ◇ ((y ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_y_pyx_pxy_Equation646 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law646 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law646.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X1))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq19 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x (M.op (M.op x x) x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq36 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = (M.op X1 (τ X0)) := by
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
  clear eq17
  have eq52 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34
    | exact resolve eq34 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq114 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq36 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq36 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq36 X0 X1
       grind)
    | exact resolve eq12 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq118 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq36 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq36 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq36 X0 X1
       grind)
    | exact resolve eq13 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (σ X2) (M.op (σ X0) (σ X2)))) = X1 ∨ (M.op (σ X0) (σ X2)) = (σ (k X0 X2)) ∨ (σ X2) = (M.op (σ X0) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (σ X2) (σ X0)
       have i₂ := eq36 X0 X2
       grind)
    | exact superpose eq36 eq9
    | (have j1 := eq36 X0 X2
       grind)
    | exact resolve eq9 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq36 X0 X1
       grind)
    | exact superpose eq36 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq36 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq36 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq36 X0 X1
       grind)
    | exact resolve eq12 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq36 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq124 : ∀ X0 X1 : G, (σ X1) = (k (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq120 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq125 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq118 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq126 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq125 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq130 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq124 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq124
    | (have j0 := eq124 X0 X1
       grind)
    | exact resolve eq124 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq131 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq126 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq126
    | (have j0 := eq126 X0 X1
       grind)
    | exact resolve eq126 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq132 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq114 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq114 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq114 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq137 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq132 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq132
    | (have j0 := eq132 X0 X1
       grind)
    | exact resolve eq132 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq457 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq37
    | exact resolve eq37 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq501 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq457 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq457
    | (have j0 := eq457 X0 X1
       grind)
    | exact resolve eq457 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq457
  have eq681 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq122 (τ X0) (τ X1)
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq122
    | (have j0 := eq122 (τ X0) (τ X1)
       grind)
    | exact resolve eq122 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq681 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq681
    | (have j0 := eq681 X0 X1
       grind)
    | exact resolve eq681 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq681
  have eq693 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq690 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq690
    | (have j0 := eq690 X0 X1
       grind)
    | exact resolve eq690 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq695 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
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
  have eq696 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq695
    | (have j0 := eq695 X0 X1
       grind)
    | exact resolve eq695 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq697 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq696 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq696
    | (have j0 := eq696 X0 X1
       grind)
    | exact resolve eq696 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq698 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq697 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq697
    | (have j0 := eq697 X0 X1
       grind)
    | exact resolve eq697 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq723 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq130 x y
       grind)
    | exact superpose eq130 eq16
    | (have j1 := eq130 x y
       grind)
    | exact resolve eq16 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130
  have eq775 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq131 X0 X1
       grind)
    | exact superpose eq131 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq131 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq131 X0 X1
       grind)
    | exact resolve eq12 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq795 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq131 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq796 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq131 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq799 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq775 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq775 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq775 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq806 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X0) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq799 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq799
    | (have j0 := eq799 X0 X1
       grind)
    | exact resolve eq799 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq799
  have eq921 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ X0) (σ (k X0 X1)))) = X2 ∨ (σ (k X0 X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq119 X0 X1 X1
       have i₂ := eq131 X0 X1
       grind)
    | exact superpose eq131 eq119
    | (have j0 := eq119 X1 X1 X0
       have j1 := eq131 X1 X0
       grind)
    | exact resolve eq119 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq131
  have eq945 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ X0) (σ (k X0 X1)))) = X2 ∨ (σ X0) = (σ (k X0 X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq921 X0 X1 X2
       have j1 := eq795 X1 X0
       grind)
    | (have r₁ := eq921 X0 X1 X2
       have r₂ := eq795 X0 X1
       grind)
    | (have r₁ := eq921 X1 X0 X2
       have r₂ := eq795 X0 X1
       grind)
    | exact resolve eq921 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq921
  have eq948 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ X0) (σ (k X0 X1)))) = X2 ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq945 X0 X1 X2
       have j1 := eq796 X1 X0
       grind)
    | (have r₁ := eq945 X1 X0 X2
       have r₂ := eq796 X0 X1
       grind)
    | exact resolve eq945 eq796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796 eq945
  have eq7339 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq723
       have i₂ := eq501 x y
       grind)
    | exact superpose eq501 eq723
    | (have j1 := eq501 x y
       grind)
    | (have r₁ := eq723
       have r₂ := eq501 x y
       grind)
    | exact resolve eq723 eq501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501 eq723
  have eq7340 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq7339
  have eq7784 : ∀ X0 X1 : G, (σ (τ X1)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (σ (k (τ X1) (τ X0))) ∨ (σ (k (τ X1) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq806 (τ X0) (τ X1)
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq806
    | (have j0 := eq806 (τ X0) (τ X1)
       grind)
    | exact resolve eq806 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7836 : ∀ X0 X1 : G, (k X0 X1) ≠ (σ (τ X1)) ∨ (σ (τ X0)) = (σ (k (τ X1) (τ X0))) ∨ (σ (k (τ X1) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7784 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq7784
    | (have j0 := eq7784 X0 X1
       grind)
    | exact resolve eq7784 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7784
  have eq7864 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (σ (τ X0)) = (σ (k (τ X1) (τ X0))) ∨ (σ (k (τ X1) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7836 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7836
    | (have j0 := eq7836 X0 X1
       grind)
    | exact resolve eq7836 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7836
  have eq7888 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (τ X1)) X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (k (τ X1) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7864 X0 X1
       have i₂ := eq18 X0 (τ X1)
       grind)
    | exact superpose eq18 eq7864
    | (have j0 := eq7864 X0 X1
       grind)
    | exact resolve eq7864 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7864
  have eq7909 : ∀ X0 X1 : G, (σ (τ X0)) = (k X1 X0) ∨ (k X0 X1) ≠ X1 ∨ (σ (k (τ X1) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7888 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7888
    | (have j0 := eq7888 X0 X1
       grind)
    | exact resolve eq7888 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7888
  have eq7928 : ∀ X0 X1 : G, (k X1 X0) = X0 ∨ (k X0 X1) ≠ X1 ∨ (σ (k (τ X1) (τ X0))) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq7909 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7909
    | (have j0 := eq7909 X0 X1
       grind)
    | exact resolve eq7909 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7909
  have eq7947 : ∀ X0 X1 : G, (σ (k (τ X1) (τ X0))) = (M.op (σ (τ X0)) X1) ∨ (k X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7928 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7928
    | (have j0 := eq7928 X0 X1
       grind)
    | exact resolve eq7928 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7928
  have eq7954 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (k (τ X1) (τ X0))) ∨ (k X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7947 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq7947
    | (have j0 := eq7947 X0 X1
       grind)
    | exact resolve eq7947 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7947
  have eq7961 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X1)) X0) ∨ (k X1 X0) = X0 ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7954 X0 X1
       have i₂ := eq18 X0 (τ X1)
       grind)
    | exact superpose eq18 eq7954
    | (have j0 := eq7954 X0 X1
       grind)
    | exact resolve eq7954 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7954
  have eq7968 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (k X1 X0) = X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq7961 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq7961
    | (have j0 := eq7961 X0 X1
       grind)
    | exact resolve eq7961 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7961
  have eq11186 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (k (τ X1) (τ X0))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq795 (τ X1) (τ X0)
       have i₂ := eq52 X0 X1
       grind)
    | exact superpose eq52 eq795
    | (have j0 := eq795 (τ X0) (τ X1)
       grind)
    | exact resolve eq795 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795
  have eq11319 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (k (σ (τ X1)) X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11186 X0 X1
       have i₂ := eq18 X0 (τ X1)
       grind)
    | exact superpose eq18 eq11186
    | (have j0 := eq11186 X0 X1
       grind)
    | exact resolve eq11186 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11186
  have eq11369 : ∀ X0 X1 : G, (k X1 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11319 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq11319
    | (have j0 := eq11319 X0 X1
       grind)
    | exact resolve eq11319 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11319
  have eq11411 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11369 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq11369
    | (have j0 := eq11369 X0 X1
       grind)
    | (have r₁ := eq11369 X1 X1
       have r₂ := eq11 (k X1 X1)
       grind)
    | exact resolve eq11369 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11369
  have eq11451 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X0)) X1) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11411 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq11411
    | (have j0 := eq11411 X0 X1
       grind)
    | exact resolve eq11411 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11411
  have eq11489 : ∀ X0 X1 : G, (M.op X0 X1) = (σ (τ (k X0 X1))) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11451 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11451
    | (have j0 := eq11451 X0 X1
       grind)
    | exact resolve eq11451 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11451
  have eq11515 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) ≠ (k X1 X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq11489 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq11489
    | (have j0 := eq11489 X0 X1
       grind)
    | exact resolve eq11489 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11489
  have eq11529 : ∀ X0 X1 : G, (M.op (σ (τ X0)) X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11515 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11515
    | (have j0 := eq11515 X0 X1
       grind)
    | exact resolve eq11515 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11515
  have eq11543 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11529 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq11529
    | (have j0 := eq11529 X0 X1
       grind)
    | exact resolve eq11529 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11529
  have eq19999 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (τ X0)) (σ (τ (k X0 X1))))) = X2 ∨ (σ (k (τ X1) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq948 (τ X0) (τ X1) X2
       have i₂ := eq52 X1 X0
       grind)
    | exact superpose eq52 eq948
    | (have j0 := eq948 (τ X0) (τ X1) X2
       grind)
    | exact resolve eq948 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq948
  have eq20192 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (τ X0)) (k X0 X1))) = X2 ∨ (σ (k (τ X1) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq19999 X0 X1 X2
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq19999
    | (have j0 := eq19999 X0 X1 X2
       grind)
    | exact resolve eq19999 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19999
  have eq20236 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (k X0 X1))) = X2 ∨ (σ (k (τ X1) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20192 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20192
    | (have j0 := eq20192 X0 X1 X2
       grind)
    | exact resolve eq20192 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20192
  have eq20269 : ∀ X0 X1 X2 : G, (σ (k (τ X1) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X2 (M.op X0 (k X0 X1))) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20236 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20236
    | (have j0 := eq20236 X0 X1 X2
       grind)
    | exact resolve eq20236 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20236
  have eq20294 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (σ (k (τ X1) (τ X0))) ∨ (M.op X2 (M.op X0 (k X0 X1))) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20269 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq20269
    | (have j0 := eq20269 X0 X1 X2
       grind)
    | exact resolve eq20269 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20269
  have eq20317 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k (σ (τ X1)) X0) ∨ (M.op X2 (M.op X0 (k X0 X1))) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20294 X0 X1 X2
       have i₂ := eq18 X0 (τ X1)
       grind)
    | exact superpose eq18 eq20294
    | (have j0 := eq20294 X0 X1 X2
       grind)
    | exact resolve eq20294 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq20294
  have eq20336 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X2 (M.op X0 (k X0 X1))) = X2 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20317 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq20317
    | (have j0 := eq20317 X0 X1 X2
       grind)
    | exact resolve eq20317 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20317
  have eq20351 : ∀ X0 X1 X2 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X2 (M.op X0 (k X0 X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20336 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq20336
    | (have j0 := eq20336 X0 X1 X2
       grind)
    | exact resolve eq20336 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20336
  have eq20360 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (k X0 X1))) = X2 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq20351 X0 X1 X2
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq20351
    | (have j0 := eq20351 X0 X1 X2
       grind)
    | exact resolve eq20351 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20351
  have eq364803 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq7340
       grind)
    | exact superpose eq7340 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq7340
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq7340
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq7340
       grind)
    | exact resolve eq12 eq7340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7340
  have eq364812 : (σ x) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq364803
  have eq364813 : (σ x) = (σ (k y x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq364812
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq364812
    | exact resolve eq364812 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364812
  have eq364814 : (k y x) = (τ (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq364813
       grind)
    | exact superpose eq364813 eq10
    | exact resolve eq10 eq364813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364813
  have eq364823 : x = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq364814
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq364814
    | exact resolve eq364814 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364814
  have eq364824 : (σ (M.op x y)) = (σ y) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq364823
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq364823
       have r₂ := eq12 x y
       grind)
    | exact resolve eq364823 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364823
  have eq364836 : (M.op x y) = (τ (σ y)) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq364824
       grind)
    | exact superpose eq364824 eq10
    | exact resolve eq10 eq364824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364824
  have eq364896 : y = (M.op x y) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq364836
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq364836
    | exact resolve eq364836 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364836
  have eq364897 : x = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have j1 := eq698 x y
       grind)
    | (have r₁ := eq364896
       have r₂ := eq698 y x
       grind)
    | exact resolve eq364896 eq698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698 eq364896
  have eq364908 : ∀ X0 : G, (M.op X0 (M.op y (M.op x y))) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 y x
       have i₂ := eq364897
       grind)
    | exact superpose eq364897 eq9
    | exact resolve eq9 eq364897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364909 : x ≠ x ∨ y = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq364897
       grind)
    | exact superpose eq364897 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq364897
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq364897
       grind)
    | exact resolve eq12 eq364897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364910 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq364897
       grind)
    | exact superpose eq364897 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq364897
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq364897
       grind)
    | exact resolve eq13 eq364897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq364959 : x ≠ x ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq364910
  have eq364960 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq364959
  have eq364961 : y = (k x y) ∨ y = (M.op x y) := by grind
  clear eq364909
  have eq364984 : (σ y) ≠ (σ y) ∨ (σ x) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq806 x y
       have i₂ := eq364961
       grind)
    | exact superpose eq364961 eq806
    | (have j0 := eq806 x y
       grind)
    | exact resolve eq806 eq364961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq364996 : y ≠ y ∨ x = (k y x) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7968 x y
       have i₂ := eq364961
       grind)
    | exact superpose eq364961 eq7968
    | (have j0 := eq7968 x y
       grind)
    | (have r₁ := eq7968 x y
       have r₂ := eq364961
       grind)
    | exact resolve eq7968 eq364961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7968
  have eq365023 : x = (k y x) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by grind
  clear eq364996
  have eq365034 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) := by grind
  clear eq364984
  have eq365048 : (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq365023
       have r₂ := eq12 y x
       grind)
    | exact resolve eq365023 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365023
  have eq365465 : x ≠ (M.op x y) ∨ x = (k y x) := by grind
  clear eq365048
  have eq394203 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (k y x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq365034
       grind)
    | exact superpose eq365034 eq16
    | exact resolve eq16 eq365034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365034
  have eq394264 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq394203
       have i₂ := eq364960
       grind)
    | exact superpose eq364960 eq394203
    | exact resolve eq394203 eq364960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364960 eq394203
  have eq394265 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq394264
  have eq394266 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) := by grind
  clear eq394265
  have eq394283 : (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq394266
       grind)
    | exact superpose eq394266 eq10
    | exact resolve eq10 eq394266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394266
  have eq394374 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq394283
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq394283
    | exact resolve eq394283 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394283
  have eq394391 : ∀ X0 : G, (M.op X0 (M.op x (M.op y x))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 X0 x y
       have i₂ := eq394374
       grind)
    | exact superpose eq394374 eq9
    | exact resolve eq9 eq394374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394392 : y ≠ y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq394374
       grind)
    | exact superpose eq394374 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq394374
       grind)
    | exact resolve eq12 eq394374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq394442 : x ≠ y ∨ x = (M.op x y) := by grind
  have eq394444 : x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq394392
  have eq394447 : x = (k y x) := by
    first
    | (have r₁ := eq394444
       have r₂ := eq365465
       grind)
    | exact resolve eq394444 eq365465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq365465 eq394444
  have eq394470 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq122 y x
       have i₂ := eq394447
       grind)
    | exact superpose eq394447 eq122
    | (have j0 := eq122 y x
       grind)
    | exact resolve eq122 eq394447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq394471 : (σ x) ≠ (σ x) ∨ (σ y) = (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq137 y x
       have i₂ := eq394447
       grind)
    | exact superpose eq394447 eq137
    | (have j0 := eq137 y x
       grind)
    | exact resolve eq137 eq394447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq394521 : x ≠ (k x y) ∨ (M.op x y) = (k x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11543 x y
       have i₂ := eq394447
       grind)
    | exact superpose eq394447 eq11543
    | (have j0 := eq11543 x y
       grind)
    | exact resolve eq11543 eq394447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11543
  have eq394554 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) := by grind
  clear eq394471
  have eq394555 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq394470
  have eq395456 : (σ (M.op x y)) ≠ (σ y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq394554
       grind)
    | exact superpose eq394554 eq16
    | exact resolve eq16 eq394554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394554
  have eq395497 : (σ y) ≠ (σ y) ∨ (σ y) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq395456
       have i₂ := eq394374
       grind)
    | exact superpose eq394374 eq395456
    | exact resolve eq395456 eq394374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395456
  have eq395501 : (σ y) = (σ (k x y)) ∨ x = (M.op x y) := by grind
  clear eq395497
  have eq395536 : (k x y) = (τ (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq395501
       grind)
    | exact superpose eq395501 eq10
    | exact resolve eq10 eq395501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395501
  have eq395630 : y = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq395536
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq395536
    | exact resolve eq395536 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395536
  have eq395687 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ (k y x) = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq20360 x y X0
       have i₂ := eq395630
       grind)
    | exact superpose eq395630 eq20360
    | (have j0 := eq20360 x y x
       grind)
    | exact resolve eq20360 eq395630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20360 eq395630
  have eq395722 : ∀ X0 : G, x = (M.op y x) ∨ (M.op X0 (M.op x y)) = X0 ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq395687 X0
       have i₂ := eq394447
       grind)
    | exact superpose eq394447 eq395687
    | (have j0 := eq395687 X0
       grind)
    | exact resolve eq395687 eq394447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394447 eq395687
  have eq395723 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op y x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq395722 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395722
  have eq402403 : x ≠ y ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq394521
       have i₂ := eq364961
       grind)
    | exact superpose eq364961 eq394521
    | exact resolve eq394521 eq364961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364961 eq394521
  have eq402404 : x ≠ y ∨ y = (M.op x y) := by grind
  clear eq402403
  have eq402623 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op y x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq395723 X0
       have i₂ := eq394374
       grind)
    | exact superpose eq394374 eq395723
    | exact resolve eq395723 eq394374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394374 eq395723
  have eq402753 : ∀ X0 : G, x = (M.op y x) ∨ (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq402623 X0
       grind)
    | (have r₁ := eq402623 X0
       have r₂ := eq394442
       grind)
    | exact resolve eq402623 eq394442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402623
  have eq402762 : ∀ X0 X1 : G, (M.op X0 (M.op x x)) = X0 ∨ x = (M.op x y) ∨ (M.op X1 y) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq394391 X0
       have i₂ := eq402753 X1
       grind)
    | exact superpose eq402753 eq394391
    | (have j1 := eq402753 x
       grind)
    | exact resolve eq394391 eq402753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394391
  have eq403011 : ∀ X0 X1 : G, (M.op X0 (M.op x x)) = X0 ∨ (M.op X1 y) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq402762 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402762
  have eq403874 : ∀ X0 X1 : G, (M.op X0 x) = X0 ∨ (M.op X1 y) = X1 ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq19 x X0
       have i₂ := eq403011 x X1
       grind)
    | exact superpose eq403011 eq19
    | (have j1 := eq403011 X0 X1
       grind)
    | exact resolve eq19 eq403011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq403011
  have eq404559 : ∀ X0 : G, x ≠ x ∨ (M.op X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq403874 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403874
  have eq404560 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq404559 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404559
  have eq405050 : ∀ X0 : G, x = y ∨ (M.op X0 y) = X0 ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq402753 X0
       have i₂ := eq404560 y
       grind)
    | exact superpose eq404560 eq402753
    | (have j0 := eq402753 X0
       grind)
    | exact resolve eq402753 eq404560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402753 eq404560
  have eq405142 : ∀ X0 : G, x = y ∨ (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq405050 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405050
  have eq405156 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq405142 X0
       grind)
    | (have r₁ := eq405142 X0
       have r₂ := eq394442
       grind)
    | exact resolve eq405142 eq394442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394442 eq405142
  have eq405733 : x ≠ x ∨ x = (M.op x y) := by
    first
    | (have j0 := eq405156 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405156
  have eq405734 : x = (M.op x y) := by grind
  clear eq405733
  have eq405773 : ∀ X0 : G, (M.op X0 (M.op y x)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq364908 X0
       have i₂ := eq405734
       grind)
    | exact superpose eq405734 eq364908
    | exact resolve eq364908 eq405734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364908
  have eq405956 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = y ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq405773 X0
       have i₂ := eq364897
       grind)
    | exact superpose eq364897 eq405773
    | exact resolve eq405773 eq364897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405773
  have eq406320 : ∀ X0 : G, (M.op X0 x) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq405956 X0
       grind)
    | (have r₁ := eq405956 X0
       have r₂ := eq402404
       grind)
    | exact resolve eq405956 eq402404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405956
  have eq406342 : ∀ X0 : G, (M.op X0 x) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq406320 X0
       have i₂ := eq405734
       grind)
    | exact superpose eq405734 eq406320
    | (have j0 := eq406320 X0
       grind)
    | exact resolve eq406320 eq405734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406320
  have eq406711 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq364897
       have i₂ := eq406342 y
       grind)
    | exact superpose eq406342 eq364897
    | exact resolve eq364897 eq406342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq364897 eq406342
  have eq406728 : x = y ∨ y = (M.op x y) := by grind
  clear eq406711
  have eq406734 : y = (M.op x y) := by
    first
    | (have r₁ := eq406728
       have r₂ := eq402404
       grind)
    | exact resolve eq406728 eq402404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402404 eq406728
  have eq406820 : x = y := by
    first
    | (have i₁ := eq406734
       have i₂ := eq405734
       grind)
    | exact superpose eq405734 eq406734
    | exact resolve eq406734 eq405734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406734
  have eq406843 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq406820
       grind)
    | exact superpose eq406820 eq16
    | exact resolve eq16 eq406820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq407085 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq394555
       have i₂ := eq406820
       grind)
    | exact superpose eq406820 eq394555
    | exact resolve eq394555 eq406820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394555
  have eq407131 : x = (M.op x x) := by
    first
    | (have i₁ := eq405734
       have i₂ := eq406820
       grind)
    | exact superpose eq406820 eq405734
    | exact resolve eq405734 eq406820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405734 eq406820
  have eq407143 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq407085
  have eq407192 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq406843
       have i₂ := eq407131
       grind)
    | exact superpose eq407131 eq406843
    | exact resolve eq406843 eq407131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406843 eq407131
  have eq407193 : False := by grind
  exact eq407193

/-- `Equation646`: `x = x ◇ (y ◇ ((y ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_pyy_pyx_Equation646 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law646 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law646.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X1))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq24 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x (M.op (M.op x x) x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (M.op (σ X1) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq54 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (M.op X1 X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq71 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq10
    | (have j1 := eq50 X1 X0
       grind)
    | exact resolve eq10 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq288 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq277 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq277
    | (have j0 := eq277 X0 X1
       grind)
    | exact resolve eq277 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq336 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq24 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq24 eq71
    | exact resolve eq71 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq368 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq336 X0 X1
       have i₂ := eq22 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq22 eq336
    | exact resolve eq336 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq377 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X1
       have i₂ := eq24 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq24 eq368
    | exact resolve eq368 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq1961 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq54
    | (have j0 := eq54 X0 X1
       grind)
    | exact resolve eq54 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq2056 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1961 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1961
    | (have j0 := eq1961 (M.op X1 X1) X1
       grind)
    | exact resolve eq1961 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1961
  have eq3176 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq288 y x
       grind)
    | exact superpose eq288 eq16
    | (have j1 := eq288 y x
       grind)
    | exact resolve eq16 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq65839 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq3176
       have i₂ := eq2056 x y
       grind)
    | exact superpose eq2056 eq3176
    | (have j1 := eq2056 (M.op y y) y
       grind)
    | (have r₁ := eq3176
       have r₂ := eq2056 x y
       grind)
    | (have r₁ := eq3176
       have r₂ := eq2056 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3176
       have r₂ := eq2056 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3176 eq2056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2056 eq3176
  have eq65840 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq65839
  have eq65841 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq65840
  have eq65851 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq65841
       grind)
    | exact superpose eq65841 eq24
    | exact resolve eq24 eq65841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65841
  have eq66537 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq65851 y
       grind)
    | exact superpose eq65851 eq24
    | exact resolve eq24 eq65851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq66544 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq377 y X0
       have i₂ := eq65851 y
       grind)
    | exact superpose eq65851 eq377
    | exact resolve eq377 eq65851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq65851
  have eq68201 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq66544 (σ x)
       grind)
    | exact superpose eq66544 eq16
    | exact resolve eq16 eq66544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66544
  have eq72337 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq68201
       have i₂ := eq66537 x
       grind)
    | exact superpose eq66537 eq68201
    | exact resolve eq68201 eq66537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66537 eq68201
  have eq72338 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq72337
  have eq72339 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq72338
  have eq72768 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq72339
       grind)
    | exact superpose eq72339 eq10
    | exact resolve eq10 eq72339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72339
  have eq72863 : x = y ∨ x = y := by
    first
    | (have i₁ := eq72768
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq72768
    | exact resolve eq72768 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72768
  have eq72864 : x = y := by grind
  clear eq72863
  have eq73352 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72864
       grind)
    | exact superpose eq72864 eq16
    | exact resolve eq16 eq72864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72864
  have eq73353 : False := by grind
  exact eq73353

/-- `Equation646`: `x = x ◇ (y ◇ ((y ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_x_pyx_Equation646 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law646 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law646.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X1))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq24 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x (M.op (M.op x x) x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (M.op (σ X1) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq54 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (M.op X1 X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq71 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq10
    | (have j1 := eq50 X1 X0
       grind)
    | exact resolve eq10 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq194 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq183 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq183
    | (have j0 := eq183 X0 X1
       grind)
    | exact resolve eq183 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq279 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq24 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq24 eq71
    | exact resolve eq71 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq305 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq279 X0 X1
       have i₂ := eq22 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq22 eq279
    | exact resolve eq279 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq314 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq305 X0 X1
       have i₂ := eq24 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq24 eq305
    | exact resolve eq305 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq1515 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq54
    | (have j0 := eq54 X0 X1
       grind)
    | exact resolve eq54 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1600 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1515 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1515
    | (have j0 := eq1515 (M.op X1 X1) X1
       grind)
    | exact resolve eq1515 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1515
  have eq2582 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq194 y x
       grind)
    | exact superpose eq194 eq16
    | (have j1 := eq194 y x
       grind)
    | exact resolve eq16 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq24029 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2582
       have i₂ := eq1600 x y
       grind)
    | exact superpose eq1600 eq2582
    | (have j1 := eq1600 (M.op y y) y
       grind)
    | (have r₁ := eq2582
       have r₂ := eq1600 x y
       grind)
    | (have r₁ := eq2582
       have r₂ := eq1600 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2582
       have r₂ := eq1600 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2582 eq1600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1600 eq2582
  have eq24030 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq24029
  have eq24031 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq24030
  have eq24037 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq24031
       grind)
    | exact superpose eq24031 eq24
    | exact resolve eq24 eq24031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24031
  have eq24451 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq24037 y
       grind)
    | exact superpose eq24037 eq24
    | exact resolve eq24 eq24037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq24456 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq314 y X0
       have i₂ := eq24037 y
       grind)
    | exact superpose eq24037 eq314
    | exact resolve eq314 eq24037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314 eq24037
  have eq25477 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq24456 (σ x)
       grind)
    | exact superpose eq24456 eq16
    | exact resolve eq16 eq24456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24456
  have eq30038 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25477
       have i₂ := eq24451 x
       grind)
    | exact superpose eq24451 eq25477
    | exact resolve eq25477 eq24451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24451 eq25477
  have eq30039 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30038
  have eq30040 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq30039
  have eq30340 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq30040
       grind)
    | exact superpose eq30040 eq10
    | exact resolve eq10 eq30040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30040
  have eq30420 : x = y ∨ x = y := by
    first
    | (have i₁ := eq30340
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30340
    | exact resolve eq30340 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30340
  have eq30421 : x = y := by grind
  clear eq30420
  have eq30730 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30421
       grind)
    | exact superpose eq30421 eq16
    | exact resolve eq16 eq30421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30421
  have eq30731 : False := by grind
  exact eq30731

/-- `Equation646`: `x = x ◇ (y ◇ ((y ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_x_pxx_y_pyx_Equation646 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law646 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law646.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X1))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X0 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq24 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x (M.op (M.op x x) x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (M.op (σ X1) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq54 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (M.op X1 X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq71 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq10
    | (have j1 := eq50 X1 X0
       grind)
    | exact resolve eq10 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq237 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq226 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq226
    | (have j0 := eq226 X0 X1
       grind)
    | exact resolve eq226 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq281 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq24 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq24 eq71
    | exact resolve eq71 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq307 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq281 X0 X1
       have i₂ := eq22 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq22 eq281
    | exact resolve eq281 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq316 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq307 X0 X1
       have i₂ := eq24 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq24 eq307
    | exact resolve eq307 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq1705 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq54 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq54
    | (have j0 := eq54 X0 X1
       grind)
    | exact resolve eq54 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1793 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1705 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1705
    | (have j0 := eq1705 (M.op X1 X1) X1
       grind)
    | exact resolve eq1705 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1705
  have eq2867 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq237 y x
       grind)
    | exact superpose eq237 eq16
    | (have j1 := eq237 y x
       grind)
    | exact resolve eq16 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq25906 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2867
       have i₂ := eq1793 x y
       grind)
    | exact superpose eq1793 eq2867
    | (have j1 := eq1793 (M.op y y) y
       grind)
    | (have r₁ := eq2867
       have r₂ := eq1793 x y
       grind)
    | (have r₁ := eq2867
       have r₂ := eq1793 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2867
       have r₂ := eq1793 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2867 eq1793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793 eq2867
  have eq25907 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq25906
  have eq25908 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq25907
  have eq25914 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq25908
       grind)
    | exact superpose eq25908 eq24
    | exact resolve eq24 eq25908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25908
  have eq26351 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq25914 y
       grind)
    | exact superpose eq25914 eq24
    | exact resolve eq24 eq25914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq26356 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq316 y X0
       have i₂ := eq25914 y
       grind)
    | exact superpose eq25914 eq316
    | exact resolve eq316 eq25914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316 eq25914
  have eq27566 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq26356 (σ x)
       grind)
    | exact superpose eq26356 eq16
    | exact resolve eq16 eq26356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26356
  have eq30342 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq27566
       have i₂ := eq26351 x
       grind)
    | exact superpose eq26351 eq27566
    | exact resolve eq27566 eq26351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26351 eq27566
  have eq30343 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30342
  have eq30344 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq30343
  have eq30685 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq30344
       grind)
    | exact superpose eq30344 eq10
    | exact resolve eq10 eq30344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30344
  have eq30766 : x = y ∨ x = y := by
    first
    | (have i₁ := eq30685
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30685
    | exact resolve eq30685 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30685
  have eq30767 : x = y := by grind
  clear eq30766
  have eq31164 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30767
       grind)
    | exact superpose eq30767 eq16
    | exact resolve eq16 eq30767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30767
  have eq31165 : False := by grind
  exact eq31165

/-- `Equation646`: `x = x ◇ (y ◇ ((y ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_x_pxy_Equation646 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law646 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law646.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq48 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq152 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq44 x y
       grind)
    | exact superpose eq44 eq16
    | (have j1 := eq44 x y
       grind)
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq157 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq918 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq48
    | exact resolve eq48 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq947 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq918 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq918
    | (have j0 := eq918 X0 X1
       grind)
    | exact resolve eq918 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq1827 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq152
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq152
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq152
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq152
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq152 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152
  have eq1828 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1827
  have eq23812 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1828
       grind)
    | exact superpose eq1828 eq16
    | exact resolve eq16 eq1828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23814 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq1828
       grind)
    | exact superpose eq1828 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq1828
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1828
       grind)
    | exact resolve eq13 eq1828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828
  have eq23830 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq23814
  have eq23831 : (σ x) = (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq23830
  have eq23833 : (σ x) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq23831
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq23831
    | exact resolve eq23831 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23831
  have eq212405 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq947 y x
       have i₂ := eq23833
       grind)
    | exact superpose eq23833 eq947
    | (have j0 := eq947 y x
       grind)
    | exact resolve eq947 eq23833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq947
  have eq212409 : (k x y) = (τ (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq10 (k x y)
       have i₂ := eq23833
       grind)
    | exact superpose eq23833 eq10
    | exact resolve eq10 eq23833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23833
  have eq212601 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq212405
  have eq212643 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq212409
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq212409
    | exact resolve eq212409 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212409
  have eq212644 : x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq212601
       have r₂ := eq23812
       grind)
    | exact resolve eq212601 eq23812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23812 eq212601
  have eq212647 : x = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq212643
       have r₂ := eq13 x y
       grind)
    | exact resolve eq212643 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212643
  have eq216575 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq157 x y
       have i₂ := eq212647
       grind)
    | exact superpose eq212647 eq157
    | (have j0 := eq157 x y
       grind)
    | exact resolve eq157 eq212647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157 eq212647
  have eq216592 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq216575
  have eq216593 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq216592
  have eq217691 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq216593
       grind)
    | exact superpose eq216593 eq16
    | exact resolve eq16 eq216593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216593
  have eq218573 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq217691
       have i₂ := eq212644
       grind)
    | exact superpose eq212644 eq217691
    | exact resolve eq217691 eq212644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212644 eq217691
  have eq218574 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq218573
  have eq218575 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq218574
  have eq219272 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq218575
       grind)
    | exact superpose eq218575 eq10
    | exact resolve eq10 eq218575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218575
  have eq219497 : x = y ∨ x = y := by
    first
    | (have i₁ := eq219272
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq219272
    | exact resolve eq219272 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219272
  have eq219498 : x = y := by grind
  clear eq219497
  have eq220734 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq219498
       grind)
    | exact superpose eq219498 eq16
    | exact resolve eq16 eq219498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219498
  have eq220735 : False := by grind
  exact eq220735

/-- `Equation646`: `x = x ◇ (y ◇ ((y ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_pyx_pxy_Equation646 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law646 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law646.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X1))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq24 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x (M.op (M.op x x) x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X1) (σ X1)) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq71 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq10
    | (have j1 := eq50 X1 X0
       grind)
    | exact resolve eq10 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq194 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq183 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq183
    | (have j0 := eq183 X0 X1
       grind)
    | exact resolve eq183 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq279 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq24 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq24 eq71
    | exact resolve eq71 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq305 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq279 X0 X1
       have i₂ := eq22 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq22 eq279
    | exact resolve eq279 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279
  have eq314 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq305 X0 X1
       have i₂ := eq24 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq24 eq305
    | exact resolve eq305 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq305
  have eq1518 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq1601 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1518 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1518
    | (have j0 := eq1518 (M.op X1 X1) X1
       grind)
    | exact resolve eq1518 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518
  have eq2561 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq194 y x
       grind)
    | exact superpose eq194 eq16
    | (have j1 := eq194 y x
       grind)
    | exact resolve eq16 eq194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq194
  have eq25093 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2561
       have i₂ := eq1601 x y
       grind)
    | exact superpose eq1601 eq2561
    | (have j1 := eq1601 (M.op y y) y
       grind)
    | (have r₁ := eq2561
       have r₂ := eq1601 x y
       grind)
    | (have r₁ := eq2561
       have r₂ := eq1601 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2561
       have r₂ := eq1601 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2561 eq1601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1601 eq2561
  have eq25094 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq25093
  have eq25095 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq25094
  have eq25101 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq25095
       grind)
    | exact superpose eq25095 eq24
    | exact resolve eq24 eq25095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25095
  have eq25543 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq25101 y
       grind)
    | exact superpose eq25101 eq24
    | exact resolve eq24 eq25101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq25548 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq314 y X0
       have i₂ := eq25101 y
       grind)
    | exact superpose eq25101 eq314
    | exact resolve eq314 eq25101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq314 eq25101
  have eq26591 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq25548 (σ x)
       grind)
    | exact superpose eq25548 eq16
    | exact resolve eq16 eq25548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25548
  have eq29996 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq26591
       have i₂ := eq25543 x
       grind)
    | exact superpose eq25543 eq26591
    | exact resolve eq26591 eq25543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25543 eq26591
  have eq29997 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq29996
  have eq29998 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq29997
  have eq30237 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq29998
       grind)
    | exact superpose eq29998 eq10
    | exact resolve eq10 eq29998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29998
  have eq30318 : x = y ∨ x = y := by
    first
    | (have i₁ := eq30237
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30237
    | exact resolve eq30237 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30237
  have eq30319 : x = y := by grind
  clear eq30318
  have eq30647 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30319
       grind)
    | exact superpose eq30319 eq16
    | exact resolve eq16 eq30319
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30319
  have eq30648 : False := by grind
  exact eq30648

/-- `Equation646`: `x = x ◇ (y ◇ ((y ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxx_x_pxy_Equation646 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law646 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law646.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X1))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq24 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x (M.op (M.op x x) x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X1) (σ X1)) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq71 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq226 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq10
    | (have j1 := eq50 X1 X0
       grind)
    | exact resolve eq10 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq237 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq226 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq226
    | (have j0 := eq226 X0 X1
       grind)
    | exact resolve eq226 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq281 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq24 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq24 eq71
    | exact resolve eq71 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq307 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq281 X0 X1
       have i₂ := eq22 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq22 eq281
    | exact resolve eq281 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq316 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq307 X0 X1
       have i₂ := eq24 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq24 eq307
    | exact resolve eq307 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq307
  have eq1705 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq1793 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1705 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1705
    | (have j0 := eq1705 (M.op X1 X1) X1
       grind)
    | exact resolve eq1705 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1705
  have eq2867 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq237 y x
       grind)
    | exact superpose eq237 eq16
    | (have j1 := eq237 y x
       grind)
    | exact resolve eq16 eq237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq25938 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq2867
       have i₂ := eq1793 x y
       grind)
    | exact superpose eq1793 eq2867
    | (have j1 := eq1793 (M.op y y) y
       grind)
    | (have r₁ := eq2867
       have r₂ := eq1793 x y
       grind)
    | (have r₁ := eq2867
       have r₂ := eq1793 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq2867
       have r₂ := eq1793 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq2867 eq1793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793 eq2867
  have eq25939 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq25938
  have eq25940 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq25939
  have eq25946 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq25940
       grind)
    | exact superpose eq25940 eq24
    | exact resolve eq24 eq25940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25940
  have eq26383 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq25946 y
       grind)
    | exact superpose eq25946 eq24
    | exact resolve eq24 eq25946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq26388 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq316 y X0
       have i₂ := eq25946 y
       grind)
    | exact superpose eq25946 eq316
    | exact resolve eq316 eq25946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316 eq25946
  have eq27598 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq26388 (σ x)
       grind)
    | exact superpose eq26388 eq16
    | exact resolve eq16 eq26388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26388
  have eq30445 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq27598
       have i₂ := eq26383 x
       grind)
    | exact superpose eq26383 eq27598
    | exact resolve eq27598 eq26383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26383 eq27598
  have eq30446 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq30445
  have eq30447 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq30446
  have eq30844 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq30447
       grind)
    | exact superpose eq30447 eq10
    | exact resolve eq10 eq30447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30447
  have eq30926 : x = y ∨ x = y := by
    first
    | (have i₁ := eq30844
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq30844
    | exact resolve eq30844 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30844
  have eq30927 : x = y := by grind
  clear eq30926
  have eq31277 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq30927
       grind)
    | exact superpose eq30927 eq16
    | exact resolve eq16 eq30927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30927
  have eq31278 : False := by grind
  exact eq31278

/-- `Equation646`: `x = x ◇ (y ◇ ((y ◇ z) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyy_y_pxy_pxx_pxy_Equation646 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law646 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law646.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X1 X2) X1))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq24 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op x (M.op (M.op x x) x))
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (M.op (σ X1) (σ X1)) (σ X1)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq50 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq44 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 X0 X1
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq71 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (σ (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq24
    | exact resolve eq24 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq277 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X0 X0) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq50 X1 X0
       grind)
    | exact superpose eq50 eq10
    | (have j1 := eq50 X1 X0
       grind)
    | exact resolve eq10 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq288 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X0) = X0 ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq277 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq277
    | (have j0 := eq277 X0 X1
       grind)
    | exact resolve eq277 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq336 : ∀ X0 X1 : G, (M.op X1 (M.op (σ (M.op X0 (M.op X0 X0))) (σ (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq71 (M.op X0 (M.op X0 X0)) X1
       have i₂ := eq24 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq24 eq71
    | exact resolve eq71 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq368 : ∀ X0 X1 : G, (M.op X1 (σ (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq336 X0 X1
       have i₂ := eq22 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq22 eq336
    | exact resolve eq336 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq377 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 (M.op X0 X0)))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq368 X0 X1
       have i₂ := eq24 X0 (M.op X0 (M.op X0 X0))
       grind)
    | exact superpose eq24 eq368
    | exact resolve eq368 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq1961 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq45 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq45
    | (have j0 := eq45 X0 X1
       grind)
    | exact resolve eq45 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq2056 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1961 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1961
    | (have j0 := eq1961 (M.op X1 X1) X1
       grind)
    | exact resolve eq1961 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1961
  have eq3176 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq288 y x
       grind)
    | exact superpose eq288 eq16
    | (have j1 := eq288 y x
       grind)
    | exact resolve eq16 eq288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288
  have eq65830 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq3176
       have i₂ := eq2056 x y
       grind)
    | exact superpose eq2056 eq3176
    | (have j1 := eq2056 (M.op y y) y
       grind)
    | (have r₁ := eq3176
       have r₂ := eq2056 x y
       grind)
    | (have r₁ := eq3176
       have r₂ := eq2056 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq3176
       have r₂ := eq2056 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq3176 eq2056
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2056 eq3176
  have eq65831 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq65830
  have eq65832 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq65831
  have eq65841 : ∀ X0 : G, (M.op X0 (M.op y y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq65832
       grind)
    | exact superpose eq65832 eq24
    | exact resolve eq24 eq65832
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65832
  have eq66527 : ∀ X0 : G, (M.op X0 y) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq24 y X0
       have i₂ := eq65841 y
       grind)
    | exact superpose eq65841 eq24
    | exact resolve eq24 eq65841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq66534 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq377 y X0
       have i₂ := eq65841 y
       grind)
    | exact superpose eq65841 eq377
    | exact resolve eq377 eq65841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq65841
  have eq68324 : (σ (M.op x y)) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq66534 (σ x)
       grind)
    | exact superpose eq66534 eq16
    | exact resolve eq16 eq66534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66534
  have eq72461 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq68324
       have i₂ := eq66527 x
       grind)
    | exact superpose eq66527 eq68324
    | exact resolve eq68324 eq66527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66527 eq68324
  have eq72462 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq72461
  have eq72463 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq72462
  have eq72892 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq72463
       grind)
    | exact superpose eq72463 eq10
    | exact resolve eq10 eq72463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72463
  have eq72988 : x = y ∨ x = y := by
    first
    | (have i₁ := eq72892
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq72892
    | exact resolve eq72892 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72892
  have eq72989 : x = y := by grind
  clear eq72988
  have eq73345 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72989
       grind)
    | exact superpose eq72989 eq16
    | exact resolve eq16 eq72989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72989
  have eq73346 : False := by grind
  exact eq73346
