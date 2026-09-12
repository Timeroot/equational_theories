import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_pyy_pxx_pyy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  clear eq43
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq85 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op x y) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq91
    | exact resolve eq91 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq93 : (M.op y y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq92
    | exact resolve eq92 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq105 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq105 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq105 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq105 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq108 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq106 (σ X0)
       grind)
    | exact superpose eq106 eq10
    | exact resolve eq10 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq106 sF2
       grind)
    | exact superpose eq106 eq49
    | exact resolve eq49 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq112 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq111
       have i₂ := eq106 x
       grind)
    | exact superpose eq106 eq111
    | exact resolve eq111 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq115 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq108 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq108
    | exact resolve eq108 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq269 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq51 (M.op sF4 sF4)
       have i₂ := eq14 sF4 sF4 sF4
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq348 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq106 (τ X0)
       grind)
    | exact superpose eq106 eq34
    | exact resolve eq34 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq359 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq348 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq348
    | exact resolve eq348 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq362 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq359 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq359
    | exact resolve eq359 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq359
  have eq544 : ∀ X0 : G, (σ X0) = (M.op y (M.op (M.op x y) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq50 (σ X0)
       have i₂ := eq115 X0
       grind)
    | exact superpose eq115 eq50
    | exact resolve eq50 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq570 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq606 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq812 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq362 X0
       grind)
    | exact superpose eq362 eq16
    | exact resolve eq16 eq362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq362
  have eq970 : ∀ X0 : G, (τ X0) = (M.op y (M.op (M.op x y) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq812 X0
       grind)
    | exact superpose eq812 eq50
    | exact resolve eq50 eq812
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq812
  have eq1392 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq269 eq271
    | exact resolve eq271 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1429 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq271 eq50
    | exact resolve eq50 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1430 : (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq271 eq51
    | exact resolve eq51 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq1449 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq269 eq1430
    | exact resolve eq1430 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1430
  have eq1450 : (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) = (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq269 eq1429
    | exact resolve eq1429 eq269
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269 eq1429
  have eq1795 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq606 X0 X0 X0
       grind)
    | exact superpose eq606 eq50
    | exact resolve eq50 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1796 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq606 X0 X0 X0
       grind)
    | exact superpose eq606 eq51
    | exact resolve eq51 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq606
  have eq1982 : (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) = (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq1449 eq1450
    | exact resolve eq1450 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1450
  have eq2081 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq570 X0
       have i₂ := eq1795 X0
       grind)
    | exact superpose eq1795 eq570
    | exact resolve eq570 eq1795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq2108 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1795 eq573
    | exact resolve eq573 eq1795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1795
  have eq2119 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq573 eq2108
    | exact resolve eq2108 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2108
  have eq2153 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq50 eq2081
    | exact resolve eq2081 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq2157 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq544 eq2081
    | exact resolve eq2081 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544 eq2081
  have eq2205 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq2153 X0
       grind)
    | exact superpose eq2153 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq2153 X0
       grind)
    | exact resolve eq13 eq2153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153
  have eq2225 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2205 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2205
  have eq2773 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1796 eq573
    | exact resolve eq573 eq1796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1796
  have eq2784 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq573 eq2773
    | exact resolve eq2773 eq573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq2773
  have eq26086 : ∀ X0 : G, (M.op (M.op (σ y) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1449 eq1392
    | exact resolve eq1392 eq1449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392 eq1449
  have eq26087 : ∀ X0 : G, (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1982 eq26086
    | exact resolve eq26086 eq1982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1982 eq26086
  have eq39250 : y = (M.op (M.op y (M.op (M.op x y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op x x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq26087 y
       have i₂ := eq93
       grind)
    | exact superpose eq93 eq26087
    | exact resolve eq26087 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq39306 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26087 eq39250
    | exact resolve eq39250 eq26087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26087 eq39250
  have eq39379 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq39306 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq39306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39380 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq39379
    | exact resolve eq39379 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39379
  have eq39391 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq39380
       have r₂ := eq27
       grind)
    | exact resolve eq39380 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39380
  have eq39395 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq39391
    | exact resolve eq39391 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39391
  have eq39442 : (τ (σ y)) = (M.op y (M.op (M.op x y) (τ (M.op (σ x) (σ x))))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq39395 eq970
    | exact resolve eq970 eq39395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39395
  have eq39548 : (τ (σ x)) = (τ (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq970 eq39442
    | exact resolve eq39442 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970 eq39442
  have eq39576 : y = (τ (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq39548
    | exact resolve eq39548 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq39548
  have eq39581 : x = y ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq39576
    | exact resolve eq39576 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq39576
  have eq39582 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq39581
  have eq39585 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq39582 eq27
    | exact resolve eq27 eq39582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39628 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq39582 eq2784
    | exact resolve eq2784 eq39582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2784
  have eq39654 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq39628
    | exact resolve eq39628 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39628
  have eq39730 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq39654 eq2225
    | exact resolve eq2225 eq39654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2225 eq39654
  have eq39853 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq39582 eq39730
    | exact resolve eq39730 eq39582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39582 eq39730
  have eq39864 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq39853
  have eq39883 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq39864 eq39306
    | exact resolve eq39306 eq39864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39306 eq39864
  have eq39892 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq39883
  have eq39896 : x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq39892
       have r₂ := eq39585
       grind)
    | exact resolve eq39892 eq39585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39585 eq39892
  have eq39910 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq39896 eq20
    | exact resolve eq20 eq39896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40005 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq39896 eq2119
    | exact resolve eq2119 eq39896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2119 eq39896
  have eq40054 : (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq40005
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq40005
    | exact resolve eq40005 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40005
  have eq40113 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq39910
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq39910
    | exact resolve eq39910 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39910
  have eq40137 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq40113 eq26
    | exact resolve eq26 eq40113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40113
  have eq40375 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2157 y
       have i₂ := eq40054
       grind)
    | exact superpose eq40054 eq2157
    | exact resolve eq2157 eq40054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2157 eq40054
  have eq40451 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq40375
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq40375
    | exact resolve eq40375 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40375
  have eq40496 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq20 eq40451
    | exact resolve eq40451 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40451
  have eq41097 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq40496 eq40137
    | exact resolve eq40137 eq40496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40137 eq40496
  have eq41142 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq41097
  have eq41150 : x = y := by
    first
    | (have r₁ := eq41142
       have r₂ := eq27
       grind)
    | exact resolve eq41142 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41142
  have eq41440 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq41150
       grind)
    | exact superpose eq41150 eq18
    | exact resolve eq18 eq41150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq41441 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq41150
       grind)
    | exact superpose eq41150 eq24
    | exact resolve eq24 eq41150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq41150
  have eq41647 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq41441
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq41441
    | exact resolve eq41441 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq41441
  have eq41686 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq41647 eq26
    | exact resolve eq26 eq41647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq41647
  have eq42220 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq41686 eq112
    | exact resolve eq112 eq41686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq41686
  have eq42404 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq42220
       have i₂ := eq41440
       grind)
    | exact superpose eq41440 eq42220
    | exact resolve eq42220 eq41440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41440 eq42220
  have eq42471 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq42404 eq15
    | exact resolve eq15 eq42404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42404
  have eq42566 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq42471
    | exact resolve eq42471 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq42471
  have eq42602 : False := by grind
  exact eq42602

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pxx_x_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
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
  have eq63 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq63
    | exact resolve eq63 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq63 X0 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq9
    | exact resolve eq9 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq65 X1 (M.op (M.op x x) (M.op X0 X0)) x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq131 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X1 X1))
       have i₂ := eq74 X1 X0
       grind)
    | exact superpose eq74 eq9
    | exact resolve eq9 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq132 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq90 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq74 X1 X1
       grind)
    | exact superpose eq74 eq90
    | exact resolve eq90 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq74 X0 X0
       grind)
    | exact superpose eq74 eq9
    | exact resolve eq9 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq171 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq131 X2 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq131 X0 X0 X0
       grind)
    | exact superpose eq131 eq131
    | exact resolve eq131 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X1 X0) X2)) = (M.op X3 (M.op (M.op X4 X3) X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq135 X2 X3 X4
       have i₂ := eq135 X2 X0 X1
       grind)
    | exact superpose eq135 eq135
    | exact resolve eq135 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq132 X2 X3
       have i₂ := eq135 X2 X0 X1
       grind)
    | exact superpose eq135 eq132
    | exact resolve eq132 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X2
       have i₂ := eq135 X2 X0 X1
       grind)
    | exact superpose eq135 eq67
    | exact resolve eq67 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq214 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X2 X2)) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq131 X2 X3 X2
       have i₂ := eq135 X2 X0 X1
       grind)
    | exact superpose eq135 eq131
    | exact resolve eq131 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq90 X2 X2
       have i₂ := eq135 X2 X0 X1
       grind)
    | exact superpose eq135 eq90
    | exact resolve eq90 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq221 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq135 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq135 eq9
    | exact resolve eq9 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq213 x x (M.op X0 X0)
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq213
    | exact resolve eq213 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq258 X0
       grind)
    | exact superpose eq258 eq12
    | (have j0 := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq258 X0
       grind)
    | exact resolve eq12 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq286 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq281 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq298 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (M.op (τ X0) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) (τ X0))
       have i₂ := eq286 (τ X0)
       grind)
    | exact superpose eq286 eq18
    | exact resolve eq18 eq286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq286
  have eq355 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op X3 (M.op X0 X0)) (M.op X0 X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq212 (M.op X3 (M.op X0 X0)) (M.op x (M.op X3 X3)) X2 X1
       have i₂ := eq131 X3 x X0
       grind)
    | exact superpose eq131 eq212
    | exact resolve eq212 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1022 : ∀ X0 X1 X2 X3 X4 : G, (M.op X2 X2) = (M.op X3 (M.op (M.op X4 X3) (M.op X0 (M.op (M.op X1 X0) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq70 X2 X2 X3 X4
       have i₂ := eq135 X2 X0 X1
       grind)
    | exact superpose eq135 eq70
    | exact resolve eq70 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1023 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X0 X0)))) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq70 X0 (M.op X1 X0) X2 X3
       have i₂ := eq135 X0 X0 X1
       grind)
    | exact superpose eq135 eq70
    | exact resolve eq70 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq1081 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1023 X0 X1 x x
       have i₂ := eq70 X0 X0 x x
       grind)
    | exact superpose eq70 eq1023
    | exact resolve eq1023 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1023
  have eq1943 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op (M.op X4 X0) (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq171 (M.op X1 (M.op (M.op X2 X1) X0)) X3 (M.op X4 X0)
       have i₂ := eq212 X1 X2 X0 X4
       grind)
    | exact superpose eq212 eq171
    | exact resolve eq171 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2087 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1943 X0 X1 X2 X3 X4
       have i₂ := eq63 X4 X0
       grind)
    | exact superpose eq63 eq1943
    | exact resolve eq1943 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1943
  have eq2126 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op (M.op X2 X1) X0) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2087 X0 X1 X2 X3 X4
       have i₂ := eq63 X1 (M.op (M.op X2 X1) X0)
       grind)
    | exact superpose eq63 eq2087
    | exact resolve eq2087 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2087
  have eq2143 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2126 X0 X1 X2 X3 X4
       have i₂ := eq212 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq212 eq2126
    | exact resolve eq2126 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2126
  have eq2148 : ∀ X0 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq2143 X0 x x X3 X4
       have i₂ := eq216 x x X0
       grind)
    | exact superpose eq216 eq2143
    | exact resolve eq2143 eq216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216 eq2143
  have eq2166 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2148 (M.op X1 X0) X2 (M.op x (M.op X1 X1))
       have i₂ := eq171 X0 x X1
       grind)
    | exact superpose eq171 eq2148
    | exact resolve eq2148 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2148
  have eq2234 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2166 X0 X1 X2
       have i₂ := eq132 X0 X1
       grind)
    | exact superpose eq132 eq2166
    | exact resolve eq2166 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2166
  have eq2249 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2234 X0 X1 X2
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq2234
    | exact resolve eq2234 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq2234
  have eq4400 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq221 (M.op X1 X1) x X1 (M.op X0 X0)
       have i₂ := eq131 X1 x X0
       grind)
    | exact superpose eq131 eq221
    | exact resolve eq221 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq221
  have eq4521 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq4400 X0 X1
       have i₂ := eq2249 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq2249 eq4400
    | exact resolve eq4400 eq2249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4400
  have eq4561 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op (M.op X1 X0) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4521 (M.op X1 X0) (M.op X1 X1)
       have i₂ := eq171 X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq171 eq4521
    | exact resolve eq4521 eq171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq171
  have eq4653 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X1 (M.op X0 X0)) X2) (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq212 (M.op X0 X0) X1 X2 (M.op X1 (M.op X0 X0))
       have i₂ := eq4521 (M.op (M.op X1 (M.op X0 X0)) X2) X0
       grind)
    | exact superpose eq4521 eq212
    | exact resolve eq212 eq4521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4521
  have eq4679 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op (M.op X1 (M.op X0 X0)) X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4653 X0 X1 X2
       have i₂ := eq2249 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X0 X0))
       grind)
    | exact superpose eq2249 eq4653
    | exact resolve eq4653 eq2249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4653
  have eq4723 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq4561 X0 X1
       have i₂ := eq2249 X0 X1 X1
       grind)
    | exact superpose eq2249 eq4561
    | exact resolve eq4561 eq2249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4561
  have eq4761 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4723 X0 X1
       have i₂ := eq132 X0 X1
       grind)
    | exact superpose eq132 eq4723
    | exact resolve eq4723 eq132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq4723
  have eq4830 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4761 (M.op (M.op X2 X1) X0) X1
       have i₂ := eq212 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq212 eq4761
    | exact resolve eq4761 eq212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq5019 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X0 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4830 (M.op X0 (M.op X2 X0)) X2 X1
       have i₂ := eq4761 X0 X2
       grind)
    | exact superpose eq4761 eq4830
    | exact resolve eq4830 eq4761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4761 eq4830
  have eq6164 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq70 X0 (M.op X1 (M.op (M.op X2 X3) (M.op X2 X3))) X3 X2
       have i₂ := eq4679 (M.op X2 X3) X1 X0
       grind)
    | exact superpose eq4679 eq70
    | exact resolve eq70 eq4679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq4679
  have eq6191 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op X1 (M.op X3 (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq6164 X0 X1 X2 X3
       have i₂ := eq2249 X3 X2 X2
       grind)
    | exact superpose eq2249 eq6164
    | exact resolve eq6164 eq2249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6164
  have eq8060 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq8075 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) ∨ (τ X0) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq8120 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8060 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq8060
    | (have j0 := eq8060 X1 X0
       have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq8060 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8060
  have eq9505 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq355 (M.op X1 (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3 X4
       have i₂ := eq214 X1 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq214 eq355
    | exact resolve eq355 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq355
  have eq9727 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op (M.op X1 (M.op X1 (M.op X0 X1))) X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9505 X0 X1 X2 X3 X4
       have i₂ := eq2249 X1 X0 X0
       grind)
    | exact superpose eq2249 eq9505
    | exact resolve eq9505 eq2249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2249 eq9505
  have eq9769 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X3) (M.op (M.op X4 (M.op X0 X1)) (M.op X1 X3))) = X3 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9727 X0 X1 X2 X3 X4
       have i₂ := eq6191 X3 X1 X0 X1
       grind)
    | exact superpose eq6191 eq9727
    | exact resolve eq9727 eq6191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6191 eq9727
  have eq12872 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X0) = (M.op (M.op X1 (M.op X2 (M.op X3 X4))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq5019 (M.op X4 X0) X1 (M.op X2 (M.op X3 X4))
       have i₂ := eq9769 X3 X4 X4 X0 X2
       grind)
    | exact superpose eq9769 eq5019
    | exact resolve eq5019 eq9769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5019 eq9769
  have eq15193 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k X0 (k (σ (τ X0)) X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq298 X0
       have i₂ := eq8075 X0 (τ X0)
       grind)
    | exact superpose eq8075 eq298
    | (have j1 := eq8075 X0 (τ X0)
       grind)
    | exact resolve eq298 eq8075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq298 eq8075
  have eq15211 : ∀ X0 : G, (k (σ (τ X0)) X0) = (k X0 (k (σ (τ X0)) X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq15193 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15193
  have eq15216 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq15211 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq15211
    | (have j0 := eq15211 X0
       grind)
    | exact resolve eq15211 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15211
  have eq30220 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op X6 X6) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6)))) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq1022 (M.op X3 (M.op X4 X5)) X2 X6 X5 X4
       have i₂ := eq198 (M.op X4 X5) X3 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) X0 X1
       grind)
    | (have i₁ := eq1022 (M.op X3 (M.op X4 X5)) X2 X6 X5 X4
       have i₂ := eq198 X0 X1 (M.op (M.op X2 (M.op X3 (M.op X4 X5))) X6) (M.op X4 X5) X3
       grind)
    | exact superpose eq198 eq1022
    | exact resolve eq1022 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq1022
  have eq30746 : ∀ X0 X1 X5 X6 : G, (M.op X6 X6) = (M.op X5 (M.op X0 (M.op (M.op X1 X0) (M.op X5 X6)))) := by
    intro X0 X1 X5 X6
    first
    | (have i₁ := eq30220 X0 X1 x x x X5 X6
       have i₂ := eq12872 X6 x x x X5
       grind)
    | exact superpose eq12872 eq30220
    | exact resolve eq30220 eq12872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12872 eq30220
  have eq111163 : ∀ X0 : G, (τ (k (σ X0) (σ X0))) = (k X0 (τ (k (σ X0) (σ X0)))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq29 X0 (k (σ X0) (σ X0))
       have i₂ := eq15216 (σ X0)
       grind)
    | exact superpose eq15216 eq29
    | (have j1 := eq15216 (σ X0)
       grind)
    | exact resolve eq29 eq15216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq15216
  have eq111210 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k X0 (k (τ (σ X0)) X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq111163 x
       have i₂ := eq23 (σ x) x
       grind)
    | exact superpose eq23 eq111163
    | (have j0 := eq111163 X0
       grind)
    | exact resolve eq111163 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq111163
  have eq111246 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq111210 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq111210
    | (have j0 := eq111210 X0
       grind)
    | exact resolve eq111210 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111210
  have eq111276 : ∀ X0 : G, (k X0 X0) = (k X0 (k X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq111246 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq111246
    | (have j0 := eq111246 X0
       grind)
    | exact resolve eq111246 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111246
  have eq111332 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 (k X0 X0)
       have i₂ := eq111276 X0
       grind)
    | exact superpose eq111276 eq14
    | (have j0 := eq14 X0 X0
       have j1 := eq111276 X0
       grind)
    | exact resolve eq14 eq111276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111276
  have eq111363 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq111332 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111332
  have eq111397 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq111363 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq111363 X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq111363 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq111363 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111363
  have eq111555 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (k X0 X0) (M.op X1 (M.op (M.op X2 X1) (k X0 X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq30746 X1 X2 (k X0 X0) X0
       have i₂ := eq111397 X0
       grind)
    | exact superpose eq111397 eq30746
    | (have j1 := eq111397 X0
       grind)
    | exact resolve eq30746 eq111397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111397
  have eq111708 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq111555 X0 x x
       have i₂ := eq213 x x (k X0 X0)
       grind)
    | exact superpose eq213 eq111555
    | (have j0 := eq111555 X0 x x
       grind)
    | exact resolve eq111555 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111555
  have eq111709 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq111708 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111708
  have eq112080 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq111709 (σ X0)
       grind)
    | exact superpose eq111709 eq15
    | exact resolve eq15 eq111709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112124 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq112080 X0
       have i₂ := eq111709 X0
       grind)
    | exact superpose eq111709 eq112080
    | exact resolve eq112080 eq111709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111709 eq112080
  have eq112387 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq8120 X0 X1
       have i₂ := eq112124 X1
       grind)
    | exact superpose eq112124 eq8120
    | (have j0 := eq8120 X0 X1
       grind)
    | exact resolve eq8120 eq112124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8120
  have eq112464 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1081 (σ X0) (σ X0)
       have i₂ := eq112124 X0
       grind)
    | exact superpose eq112124 eq1081
    | exact resolve eq1081 eq112124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq154093 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq112387 x y
       grind)
    | exact superpose eq112387 eq16
    | (have j1 := eq112387 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq112387 x y
       grind)
    | exact resolve eq16 eq112387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112387
  have eq154444 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq154093
  have eq176666 : ∀ X0 X1 : G, (M.op (σ y) (σ y)) = (M.op (σ x) (M.op X0 (M.op (M.op X1 X0) (σ x)))) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq30746 X0 X1 (σ x) (σ y)
       have i₂ := eq154444
       grind)
    | exact superpose eq154444 eq30746
    | exact resolve eq30746 eq154444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154444
  have eq176739 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq176666 x x
       have i₂ := eq213 x x (σ x)
       grind)
    | exact superpose eq213 eq176666
    | exact resolve eq176666 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176666
  have eq176759 : (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq176739
       have i₂ := eq112124 y
       grind)
    | exact superpose eq112124 eq176739
    | exact resolve eq176739 eq112124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112124 eq176739
  have eq176760 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq176759
  have eq176781 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq176760
  have eq176792 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq176781
  have eq239055 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq176792
       grind)
    | exact superpose eq176792 eq10
    | exact resolve eq10 eq176792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176792
  have eq239326 : x = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq239055
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq239055
    | exact resolve eq239055 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239055
  have eq239327 : x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq239326
  have eq239570 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1081 y y
       have i₂ := eq239327
       grind)
    | exact superpose eq239327 eq1081
    | exact resolve eq1081 eq239327
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1081 eq239327
  have eq239708 : x = (M.op x y) := by grind
  clear eq239570
  have eq239912 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq239708
       grind)
    | exact superpose eq239708 eq16
    | exact resolve eq16 eq239708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239984 : ∀ X0 X1 : G, (M.op y y) = (M.op x (M.op X0 (M.op (M.op X1 X0) x))) := by
    intro X0 X1
    first
    | (have i₁ := eq30746 X0 X1 x y
       have i₂ := eq239708
       grind)
    | exact superpose eq239708 eq30746
    | exact resolve eq30746 eq239708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30746 eq239708
  have eq240082 : x = (M.op y y) := by
    first
    | (have i₁ := eq239984 x x
       have i₂ := eq213 x x x
       grind)
    | exact superpose eq213 eq239984
    | exact resolve eq239984 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq239984
  have eq240433 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq112464 y
       have i₂ := eq240082
       grind)
    | exact superpose eq240082 eq112464
    | exact resolve eq112464 eq240082
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112464 eq240082
  have eq240729 : False := by grind
  exact eq240729

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxx_y_pyx_x_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq97 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq44 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq44
    | (have j0 := eq44 x
       grind)
    | exact resolve eq44 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
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
  have eq174 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq16 X0 X2 X1
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq16 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq186 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq175 (M.op sF4 sF4)
       have i₂ := eq16 sF4 sF4 sF4
       grind)
    | exact superpose eq16 eq175
    | exact resolve eq175 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq189 : (M.op (σ x) (σ y)) ≠ (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq186 eq13
    | exact resolve eq13 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq186 eq175
    | exact resolve eq175 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op X1 X0) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq186 eq16
    | exact resolve eq16 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq321 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq405 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq321 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq321
    | exact resolve eq321 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq557 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq191 eq193
    | exact resolve eq193 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq193
  have eq561 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y))))) := by
    first
    | (have i₁ := eq557
       have i₂ := eq177 sF4 (M.op sF3 sF4)
       grind)
    | exact superpose eq177 eq557
    | exact resolve eq557 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557
  have eq597 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq186 eq11
    | exact resolve eq11 eq186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq186
  have eq604 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
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
  have eq610 : (M.op x y) = (k x y) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
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
  have eq621 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
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
  have eq646 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X0 X0))) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq604 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq650 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (σ x) (σ y))) := by grind
  clear eq597
  have eq658 : (M.op (σ y) (M.op (σ x) (σ y))) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq650
       have r₂ := eq189
       grind)
    | exact resolve eq650 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq189 eq650
  have eq661 : (M.op (σ x) (σ y)) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    first
    | exact superpose eq658 eq561
    | exact resolve eq561 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq668 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq658 eq16
    | exact resolve eq16 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq733 : (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq668 (M.op (k sF4 sF4) (k sF4 sF4))
       have i₂ := eq16 (k sF4 sF4) (k sF4 sF4) (k sF4 sF4)
       grind)
    | exact superpose eq16 eq668
    | exact resolve eq668 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq771 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (M.op x y) (M.op X0 X0)) X0) := by
    intro X0
    first
    | exact superpose eq174 eq177
    | exact resolve eq177 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq784 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 X0
       have i₂ := eq177 X0 X0
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq787 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq177 X0 X1
       grind)
    | exact superpose eq177 eq11
    | exact resolve eq11 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq789 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 (M.op X1 X0)) ∨ (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq177 X0 X1
       grind)
    | exact superpose eq177 eq13
    | exact resolve eq13 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq793 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op X1 X0)
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq175
    | exact resolve eq175 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq794 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq174 (M.op X1 X0)
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq174
    | exact resolve eq174 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq795 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X1 X0) X2 X3
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq16
    | exact resolve eq16 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq796 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) ∨ (M.op X1 X0) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq787 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787
  have eq798 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X0)) = (k (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq796 X0 X1
       have j1 := eq789 X0 X1
       grind)
    | (have r₁ := eq796 X0 X1
       have r₂ := eq789 X0 X1
       grind)
    | exact resolve eq796 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789 eq796
  have eq833 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq784 X0
       grind)
    | exact superpose eq784 eq16
    | exact resolve eq16 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq951 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq771 eq16
    | exact resolve eq16 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771
  have eq964 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq951 X0
       have i₂ := eq177 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq177 eq951
    | exact resolve eq951 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq969 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq964 X0
       have i₂ := eq177 X0 X0
       grind)
    | exact superpose eq177 eq964
    | exact resolve eq964 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq1029 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq176 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3 X4
       have i₂ := eq176 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1040 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq176 X4 X2 X3 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq176 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1057 : ∀ X0 X1 X4 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X4 X4))) = X4 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq16 X4 (M.op X1 (M.op X0 X0)) (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq176 X1 x x X0
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1058 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq177 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq176 X0 x x X3
       grind)
    | exact superpose eq176 eq177
    | exact resolve eq177 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1062 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq176 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1064 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq175 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq176 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq176 eq175
    | exact resolve eq175 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1065 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (σ x) (σ y)) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq668 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq176 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq176 eq668
    | exact resolve eq668 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1076 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op (M.op (σ x) (σ y)) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1065 X0 X1
       have i₂ := eq177 X0 X1
       grind)
    | exact superpose eq177 eq1065
    | exact resolve eq1065 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq1077 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq1064 X0 X1
       have i₂ := eq177 X0 X1
       grind)
    | exact superpose eq177 eq1064
    | exact resolve eq1064 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq1079 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1062 X0 X1 X2 X3
       have i₂ := eq177 X0 X1
       grind)
    | exact superpose eq177 eq1062
    | exact resolve eq1062 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq1089 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) = (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1040 X0 X1 X2 X3 X4
       have i₂ := eq177 X0 X1
       grind)
    | exact superpose eq177 eq1040
    | exact resolve eq1040 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1040
  have eq1091 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1029 X0 X1 X2 X3 X4
       have i₂ := eq177 X0 X1
       grind)
    | exact superpose eq177 eq1029
    | exact resolve eq1029 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq1094 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1079 X0 X1 X2 X3
       have i₂ := eq1077 X0 X1
       grind)
    | exact superpose eq1077 eq1079
    | exact resolve eq1079 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1077 eq1079
  have eq1099 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X4 X4)) (M.op X4 (M.op X0 X1))) = (M.op (M.op (σ x) (σ y)) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1089 X0 X1 X2 X3 X4
       have i₂ := eq1076 X0 X1
       grind)
    | exact superpose eq1076 eq1089
    | exact resolve eq1089 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq1100 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X2 X3) (M.op X0 X1)) (M.op (M.op (M.op (σ x) (σ y)) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X1))) (M.op X4 X4))) = X4 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq1091 X0 X1 X2 X3 X4
       have i₂ := eq1076 X0 X1
       grind)
    | exact superpose eq1076 eq1091
    | exact resolve eq1091 eq1076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1076 eq1091
  have eq1208 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1058 X1 x
       have i₂ := eq11 X1 X1
       grind)
    | exact superpose eq11 eq1058
    | (have j1 := eq11 X0 X0
       grind)
    | exact resolve eq1058 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1209 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 (M.op X0 (M.op X1 X0))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1058 (M.op X0 X1) x
       have i₂ := eq177 X0 X1
       grind)
    | exact superpose eq177 eq1058
    | exact resolve eq1058 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1236 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1208 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1208
  have eq1892 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq610
       grind)
    | exact superpose eq610 eq40
    | exact resolve eq40 eq610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq610
  have eq1893 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1892
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1892
    | exact resolve eq1892 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1892
  have eq1895 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq1893
    | exact resolve eq1893 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1893
  have eq2063 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq793 (M.op X0 X0) X0
       have i₂ := eq969 X0
       grind)
    | exact superpose eq969 eq793
    | exact resolve eq793 eq969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2211 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq969 X0
       have i₂ := eq2063 X0
       grind)
    | exact superpose eq2063 eq969
    | exact resolve eq969 eq2063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2214 : ∀ X0 : G, (M.op X0 (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq784 X0
       have i₂ := eq2063 X0
       grind)
    | exact superpose eq2063 eq784
    | exact resolve eq784 eq2063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq2217 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq1058 X0 X0
       have i₂ := eq2063 X0
       grind)
    | exact superpose eq2063 eq1058
    | exact resolve eq1058 eq2063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2219 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0
    first
    | (have i₁ := eq793 X0 X0
       have i₂ := eq2063 X0
       grind)
    | exact superpose eq2063 eq793
    | exact resolve eq793 eq2063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2223 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | (have i₁ := eq177 X0 (M.op X0 X0)
       have i₂ := eq2063 X0
       grind)
    | exact superpose eq2063 eq177
    | exact resolve eq177 eq2063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2260 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) := by
    intro X0
    first
    | (have i₁ := eq2223 X0
       have i₂ := eq177 sF3 (M.op sF4 X0)
       grind)
    | exact superpose eq177 eq2223
    | exact resolve eq2223 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2223
  have eq2268 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2211 eq2260
    | exact resolve eq2260 eq2211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260
  have eq2427 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq175 eq2214
    | exact resolve eq2214 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq2214
  have eq2621 : ∀ X0 : G, (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X0)) = (M.op (M.op (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X0)) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X0))) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq668 eq2211
    | exact resolve eq2211 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2672 : ∀ X0 : G, (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X0)) = (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X0)))))) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq2621 X0
       have i₂ := eq2219 (M.op (k sF4 sF4) (M.op X0 X0))
       grind)
    | exact superpose eq2219 eq2621
    | exact resolve eq2621 eq2219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2219 eq2621
  have eq2687 : ∀ X0 : G, (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X0)) = (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq668 eq2672
    | exact resolve eq2672 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2672
  have eq2697 : ∀ X0 : G, (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X0)) = (M.op (M.op (σ y) X0) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq2217 eq2687
    | exact resolve eq2687 eq2217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217 eq2687
  have eq2703 : ∀ X0 : G, (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X0)) = (M.op X0 (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq2697 x
       have i₂ := eq177 sF3 x
       grind)
    | exact superpose eq177 eq2697
    | exact resolve eq2697 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2697
  have eq3255 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X1 (M.op (M.op X2 X1) (k X0 X0))
       have i₂ := eq646 X0 X1 X2
       grind)
    | exact superpose eq646 eq177
    | (have j1 := eq646 X0 X1 X2
       grind)
    | exact resolve eq177 eq646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq3275 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq1236 eq3255
    | (have j0 := eq3255 X0 x x
       have j1 := eq1236 X0 x
       grind)
    | exact resolve eq3255 eq1236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1236 eq3255
  have eq3298 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq3275 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq3275 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq3275 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3275
  have eq3325 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (k X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq3298 X0
       grind)
    | exact superpose eq3298 eq16
    | exact resolve eq16 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3333 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op X1 X1)) (M.op X1 (k X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq188 X1 X0
       have i₂ := eq3298 X0
       grind)
    | exact superpose eq3298 eq188
    | exact resolve eq188 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq3342 : ∀ X0 : G, (M.op (k X0 X0) (M.op X0 (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq969 X0
       have i₂ := eq3298 X0
       grind)
    | exact superpose eq3298 eq969
    | exact resolve eq969 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq3345 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq2063 X0
       have i₂ := eq3298 X0
       grind)
    | exact superpose eq3298 eq2063
    | exact resolve eq2063 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3346 : ∀ X0 : G, (M.op (k X0 X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq2211 X0
       have i₂ := eq3298 X0
       grind)
    | exact superpose eq3298 eq2211
    | exact resolve eq2211 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2211
  have eq3349 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2427 X0
       have i₂ := eq3298 X0
       grind)
    | exact superpose eq3298 eq2427
    | exact resolve eq2427 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2427
  have eq3350 : ∀ X0 X1 : G, (M.op X0 (M.op (k X0 X0) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X0 X0
       have i₂ := eq3298 X0
       grind)
    | exact superpose eq3298 eq16
    | exact resolve eq16 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3352 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq177 X0 X0
       have i₂ := eq3298 X0
       grind)
    | exact superpose eq3298 eq177
    | exact resolve eq177 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3357 : ∀ X0 : G, (k X0 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq793 X0 X0
       have i₂ := eq3298 X0
       grind)
    | exact superpose eq3298 eq793
    | exact resolve eq793 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3460 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (k (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3352 X0
       have i₂ := eq3298 (k X0 X0)
       grind)
    | exact superpose eq3298 eq3352
    | exact resolve eq3352 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3352
  have eq3461 : ∀ X0 X1 : G, (M.op X0 (M.op (k X0 X0) (k X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3350 X0 X1
       have i₂ := eq3298 X1
       grind)
    | exact superpose eq3298 eq3350
    | exact resolve eq3350 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3350
  have eq3462 : ∀ X0 X1 : G, (M.op (M.op (M.op (σ x) (σ y)) (k X1 X1)) (M.op X1 (k X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3333 X0 X1
       have i₂ := eq3298 X1
       grind)
    | exact superpose eq3298 eq3333
    | exact resolve eq3333 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3333
  have eq3817 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) (M.op X0 (k X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq2268 eq3325
    | exact resolve eq3325 eq2268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3847 : ∀ X0 X1 : G, (M.op (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X0)) (M.op X0 (k X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq668 eq3325
    | exact resolve eq3325 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3854 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (k X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3325 (σ X0) X1 X2
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq3325
    | exact resolve eq3325 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3905 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op (σ y) X0)) (M.op X0 (k X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq2703 eq3847
    | exact resolve eq3847 eq2703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3847
  have eq4272 : ∀ X0 X1 : G, (M.op (τ X0) (M.op (τ (k X0 X0)) (k X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3461 (τ X0) X1
       have i₂ := eq405 X0 X0
       grind)
    | exact superpose eq405 eq3461
    | exact resolve eq3461 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405
  have eq4303 : (k (M.op x y) (M.op x y)) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq174 (k sF0 sF0)
       have i₂ := eq3461 sF0 sF0
       grind)
    | exact superpose eq3461 eq174
    | exact resolve eq174 eq3461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq8734 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq2268 eq794
    | exact resolve eq794 eq2268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8738 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq794 (k X0 X0) X0
       have i₂ := eq3342 X0
       grind)
    | exact superpose eq3342 eq794
    | exact resolve eq794 eq3342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq9084 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (k y y)))) := by
    first
    | exact superpose eq8738 eq793
    | exact resolve eq793 eq8738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9089 : ∀ X0 : G, (M.op (M.op X0 (k X0 X0)) (M.op X0 (k X0 X0))) = (M.op (M.op (M.op x y) X0) (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | exact superpose eq8738 eq177
    | exact resolve eq177 eq8738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8738
  have eq9107 : ∀ X0 : G, (k (M.op X0 (k X0 X0)) (M.op X0 (k X0 X0))) = (M.op (M.op (M.op x y) X0) (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9089 X0
       have i₂ := eq3298 (M.op X0 (k X0 X0))
       grind)
    | exact superpose eq3298 eq9089
    | exact resolve eq9089 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9089
  have eq9110 : (k y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq3357 eq9084
    | exact resolve eq9084 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9084
  have eq9163 : ∀ X0 : G, (M.op (k X0 X0) (M.op X0 (k X0 X0))) = (M.op (M.op (M.op x y) X0) (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq9107 X0
       have i₂ := eq798 (k X0 X0) X0
       grind)
    | exact superpose eq798 eq9107
    | exact resolve eq9107 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9107
  have eq9185 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op X0 (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9163 X0
       have i₂ := eq3342 X0
       grind)
    | exact superpose eq3342 eq9163
    | exact resolve eq9163 eq3342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9163
  have eq9267 : ∀ X0 : G, (M.op y X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (k (M.op x y) (M.op x y)) (k X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq8734 (M.op (k sF0 sF0) (k x x))
       have i₂ := eq3461 sF0 x
       grind)
    | exact superpose eq3461 eq8734
    | exact resolve eq8734 eq3461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9364 : ∀ X0 : G, (M.op (k (M.op x y) (M.op x y)) (k X0 X0)) = (M.op X0 (M.op (M.op (k (M.op x y) (M.op x y)) (k X0 X0)) (k (M.op (k (M.op x y) (M.op x y)) (k X0 X0)) (M.op (k (M.op x y) (M.op x y)) (k X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq9185 (M.op (k sF0 sF0) (k x x))
       have i₂ := eq3461 sF0 x
       grind)
    | exact superpose eq3461 eq9185
    | exact resolve eq9185 eq3461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9185
  have eq9412 : ∀ X0 : G, (M.op (k (M.op x y) (M.op x y)) (k X0 X0)) = (M.op X0 (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (k (M.op x y) (M.op x y)) (k X0 X0))))) := by
    intro X0
    first
    | (have i₁ := eq9364 X0
       have i₂ := eq3345 (M.op (k sF0 sF0) (k X0 X0))
       grind)
    | exact superpose eq3345 eq9364
    | exact resolve eq9364 eq3345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9364
  have eq9432 : ∀ X0 : G, (M.op (k (M.op x y) (M.op x y)) (k X0 X0)) = (M.op X0 (M.op y X0)) := by
    intro X0
    first
    | exact superpose eq9267 eq9412
    | exact resolve eq9412 eq9267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9267 eq9412
  have eq10232 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq1057 X0 X0 X0
       grind)
    | exact superpose eq1057 eq16
    | exact resolve eq16 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10245 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op (σ x) (σ y)) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | (have i₁ := eq668 (M.op X0 (M.op X0 X0))
       have i₂ := eq1057 X0 X0 X0
       grind)
    | exact superpose eq1057 eq668
    | exact resolve eq668 eq1057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq10254 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    have f10254_11 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
      intro X0 X1
      grind
    have f10254_12 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
      intro X0 X1 X2
      grind
    have f10254_20 : X0 ≠ (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) := by grind
    have f10254_86 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f10254_11 (M.op x (M.op x x)) X1
         have i₂ := f10254_12 x x x
         grind)
      | exact superpose f10254_12 f10254_11
      | exact resolve f10254_11 f10254_12
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f10254_126 : X0 ≠ X0 := by
      first
      | (have i₁ := f10254_20
         have i₂ := f10254_86 X0 X1
         grind)
      | exact superpose f10254_86 f10254_20
      | (have r₁ := f10254_20
         have r₂ := f10254_86 X0 X1
         grind)
      | exact resolve f10254_20 f10254_86
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f10254_129 : False := by grind
    exact f10254_129
  clear eq1057 eq1058
  have eq10294 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (k X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10254 X0 X1
       have i₂ := eq3298 X0
       grind)
    | exact superpose eq3298 eq10254
    | exact resolve eq10254 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10254
  have eq10301 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op (M.op (σ x) (σ y)) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | (have i₁ := eq10245 X0
       have i₂ := eq3298 X0
       grind)
    | exact superpose eq3298 eq10245
    | exact resolve eq10245 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10245
  have eq10311 : ∀ X0 X1 X2 : G, (M.op X0 (k X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10232 X0 X1 X2
       have i₂ := eq3298 X0
       grind)
    | exact superpose eq3298 eq10232
    | exact resolve eq10232 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10232
  have eq10690 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10294 X0 X1
       have i₂ := eq3345 X0
       grind)
    | exact superpose eq3345 eq10294
    | exact resolve eq10294 eq3345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15398 : ∀ X0 : G, (M.op X0 (k X0 X0)) = (M.op y (M.op (k y y) X0)) := by
    intro X0
    first
    | exact superpose eq9110 eq10311
    | exact resolve eq10311 eq9110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15474 : ∀ X0 X1 X2 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X2)) = (M.op X0 (M.op (M.op X1 X0) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3345 X2
       have i₂ := eq10311 X2 X0 X1
       grind)
    | exact superpose eq10311 eq3345
    | exact resolve eq3345 eq10311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15480 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq10294 X2 X3
       have i₂ := eq10311 X2 X0 X1
       grind)
    | exact superpose eq10311 eq10294
    | exact resolve eq10294 eq10311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15518 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq793 X0 (M.op X1 X0)
       have i₂ := eq10311 X0 X0 X1
       grind)
    | exact superpose eq10311 eq793
    | exact resolve eq793 eq10311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15578 : ∀ X0 X1 : G, (k X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq3357 eq15518
    | exact resolve eq15518 eq3357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3357 eq15518
  have eq26411 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ X0))) = (M.op (M.op X1 (σ (k X0 X0))) (σ (k X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq793 (σ (k X0 X0)) (M.op X1 (σ (k X0 X0)))
       have i₂ := eq3854 X0 (σ (k X0 X0)) X1
       grind)
    | exact superpose eq3854 eq793
    | exact resolve eq793 eq3854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793 eq3854
  have eq26475 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ X0))) = (k (σ (k X0 X0)) (σ (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26411 X0 x
       have i₂ := eq15578 (σ (k X0 X0)) x
       grind)
    | exact superpose eq15578 eq26411
    | exact resolve eq26411 eq15578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26411
  have eq26576 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ X0))) = (σ (k (k X0 X0) (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26475 X0
       have i₂ := eq10 (k X0 X0) (k X0 X0)
       grind)
    | exact superpose eq10 eq26475
    | exact resolve eq26475 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26475
  have eq26628 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ X0))) = (σ (M.op X0 (k X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26576 X0
       have i₂ := eq3460 X0
       grind)
    | exact superpose eq3460 eq26576
    | exact resolve eq26576 eq3460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3460 eq26576
  have eq27687 : ∀ X0 : G, (M.op (τ (σ (M.op x y))) (M.op (k (M.op x y) (M.op x y)) (k X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq133 eq4272
    | exact resolve eq4272 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq4272
  have eq27752 : ∀ X0 : G, (M.op (τ (σ (M.op x y))) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq9432 eq27687
    | exact resolve eq27687 eq9432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27687
  have eq27846 : ∀ X0 : G, (M.op (M.op x y) (M.op X0 (M.op y X0))) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq27752
    | exact resolve eq27752 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27752
  have eq27933 : ∀ X0 X1 : G, (M.op (M.op X1 y) X0) = (M.op (M.op x y) (M.op (M.op (M.op X1 y) X0) (M.op X0 (k X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq27846 (M.op (M.op X1 y) X0)
       have i₂ := eq10311 X0 y X1
       grind)
    | exact superpose eq10311 eq27846
    | exact resolve eq27846 eq10311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27977 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op y X0)) (M.op X0 (k X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq27846 eq3325
    | exact resolve eq3325 eq27846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27846
  have eq28020 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X1 y) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq27933 X0 X1
       have i₂ := eq10294 X0 (M.op X1 y)
       grind)
    | exact superpose eq10294 eq27933
    | exact resolve eq27933 eq10294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10294 eq27933
  have eq28209 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (k y y) X0) := by
    intro X0
    first
    | exact superpose eq9110 eq28020
    | exact resolve eq28020 eq9110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9110 eq28020
  have eq31545 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op x y) (M.op (k (M.op x y) (M.op x y)) X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq4303 eq15480
    | exact resolve eq15480 eq4303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4303
  have eq33871 : ∀ X0 : G, (M.op (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq733 eq833
    | exact resolve eq833 eq733
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq733 eq833
  have eq33926 : ∀ X0 : G, (M.op (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq2703 eq33871
    | exact resolve eq33871 eq2703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33871
  have eq33956 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op (σ y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq661 eq33926
    | exact resolve eq33926 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661 eq33926
  have eq34051 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X1 (σ y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq33956 (M.op (M.op X1 sF3) x)
       have i₂ := eq15480 sF3 X1 x (M.op X1 sF3)
       grind)
    | exact superpose eq15480 eq33956
    | exact resolve eq33956 eq15480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33956
  have eq40418 : ∀ X0 X1 : G, (M.op (M.op X1 (k X0 X0)) (k (M.op X1 (k X0 X0)) (M.op X1 (k X0 X0)))) = (M.op (M.op (σ y) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq3905 eq10311
    | exact resolve eq10311 eq3905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10311
  have eq40479 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X1 (k X0 X0)))) = (M.op (M.op (σ y) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq40418 X0 X1
       have i₂ := eq3345 (M.op X1 (k X0 X0))
       grind)
    | exact superpose eq3345 eq40418
    | exact resolve eq40418 eq3345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40418
  have eq41972 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op (σ x) (σ y)) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) := by
    intro X0
    first
    | (have i₁ := eq3345 X0
       have i₂ := eq10301 X0
       grind)
    | exact superpose eq10301 eq3345
    | exact resolve eq3345 eq10301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3345 eq10301
  have eq47684 : ∀ X0 X1 : G, (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 (M.op X1 X0))) = (M.op (M.op X1 X0) (M.op (σ y) (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2703 (M.op X1 X0)
       have i₂ := eq177 X1 X0
       grind)
    | exact superpose eq177 eq2703
    | exact resolve eq2703 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq2703
  have eq50407 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X1 (k X0 X0)))) = (M.op (M.op (M.op (σ x) (σ y)) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq3817 eq15474
    | exact resolve eq15474 eq3817
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3817
  have eq50451 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (M.op X1 (M.op X2 X3)) (k X0 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq15474 X3 X2 (M.op (M.op X1 (M.op X2 X3)) (k X0 X0))
       have i₂ := eq3325 X0 (M.op X2 X3) X1
       grind)
    | exact superpose eq3325 eq15474
    | exact resolve eq15474 eq3325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3325
  have eq50609 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) X0) = (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) (M.op (σ y) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2268 (M.op (M.op X1 sF4) x)
       have i₂ := eq15474 sF4 X1 x
       grind)
    | exact superpose eq15474 eq2268
    | exact resolve eq2268 eq15474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50631 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op (σ x) (σ y))) X0) = (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)))) := by
    intro X0 X1
    first
    | exact superpose eq47684 eq50609
    | exact resolve eq50609 eq47684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47684 eq50609
  have eq50711 : ∀ X0 X1 X2 X3 : G, (M.op X3 X0) = (M.op (M.op (σ y) (M.op X1 (M.op X2 X3))) X0) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq40479 eq50451
    | exact resolve eq50451 eq40479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50451
  have eq50738 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) X0) = (M.op (M.op (M.op (σ x) (σ y)) X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq40479 eq50407
    | exact resolve eq50407 eq40479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50407
  have eq50839 : ∀ X0 X1 : G, (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0) = (M.op (M.op X1 (M.op (σ x) (σ y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq10690 eq50631
    | exact resolve eq50631 eq10690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50631
  have eq53854 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X1 (k X0 X0)))) = (M.op (M.op y X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq15474 (M.op y X1) X1 (M.op X1 (k X0 X0))
       have i₂ := eq27977 X1 X0
       grind)
    | exact superpose eq27977 eq15474
    | exact resolve eq15474 eq27977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27977
  have eq53926 : ∀ X0 X1 : G, (M.op (M.op (σ y) X1) X0) = (M.op (M.op y X1) X0) := by
    intro X0 X1
    first
    | exact superpose eq40479 eq53854
    | exact resolve eq53854 eq40479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53854
  have eq54160 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) X1) = (M.op (M.op (σ y) (M.op (M.op x y) X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq8734 eq53926
    | exact resolve eq53926 eq8734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73288 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op y (M.op X1 X0))) = (M.op (k (M.op x y) (M.op x y)) (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq9432 (M.op X1 X0)
       have i₂ := eq798 X0 X1
       grind)
    | exact superpose eq798 eq9432
    | exact resolve eq9432 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9432
  have eq74659 : ∀ X0 : G, (M.op (k X0 X0) (M.op y (M.op (k y y) X0))) = (k (M.op y (M.op (k y y) X0)) (M.op y (M.op (k y y) X0))) := by
    intro X0
    first
    | (have i₁ := eq798 (k X0 X0) X0
       have i₂ := eq15398 X0
       grind)
    | exact superpose eq15398 eq798
    | exact resolve eq798 eq15398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15398
  have eq74847 : ∀ X0 : G, (M.op (k X0 X0) (M.op y (M.op (k y y) X0))) = (M.op (M.op (k y y) X0) (M.op y (M.op (k y y) X0))) := by
    intro X0
    first
    | (have i₁ := eq74659 X0
       have i₂ := eq798 (M.op (k y y) X0) y
       grind)
    | exact superpose eq798 eq74659
    | exact resolve eq74659 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74659
  have eq74977 : ∀ X0 : G, (M.op (k X0 X0) (M.op y (M.op (k y y) X0))) = (M.op (k (M.op x y) (M.op x y)) (M.op X0 (M.op (k y y) X0))) := by
    intro X0
    first
    | (have i₁ := eq74847 X0
       have i₂ := eq73288 X0 (k y y)
       grind)
    | exact superpose eq73288 eq74847
    | exact resolve eq74847 eq73288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73288 eq74847
  have eq75048 : ∀ X0 : G, (M.op (k X0 X0) (M.op y (M.op (M.op x y) X0))) = (M.op (k (M.op x y) (M.op x y)) (M.op X0 (M.op (M.op x y) X0))) := by
    intro X0
    first
    | (have i₁ := eq74977 X0
       have i₂ := eq28209 X0
       grind)
    | exact superpose eq28209 eq74977
    | exact resolve eq74977 eq28209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74977
  have eq75085 : ∀ X0 : G, (M.op (k X0 X0) (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0))) = (M.op (k (M.op x y) (M.op x y)) (M.op X0 (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq8734 eq75048
    | exact resolve eq75048 eq8734
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75048
  have eq75102 : ∀ X0 : G, (M.op (k (M.op x y) (M.op x y)) (M.op X0 (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq3346 eq75085
    | exact resolve eq75085 eq3346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3346 eq75085
  have eq75159 : ∀ X0 X1 : G, (M.op (k (M.op x y) (M.op x y)) X0) = (M.op (M.op X1 (M.op x y)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq75102 (M.op (M.op X1 sF0) x)
       have i₂ := eq15480 sF0 X1 x (M.op X1 sF0)
       grind)
    | exact superpose eq15480 eq75102
    | exact resolve eq75102 eq15480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75102
  have eq77064 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X2))) = (M.op (M.op X1 X2) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq795 (M.op X0 (M.op X1 X2)) (M.op X1 X2) X2 X1
       have i₂ := eq795 (M.op X1 X2) X0 (M.op X1 X2) X0
       grind)
    | exact superpose eq795 eq795
    | exact resolve eq795 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77180 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X2 (σ y)) (M.op X1 (M.op X0 X1))) (M.op X0 X1)) (M.op (M.op (M.op X2 (σ y)) (M.op X1 (M.op X0 X1))) (k X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq3905 (M.op (M.op X3 sF3) (M.op X0 (M.op X1 X0))) X1
       have i₂ := eq795 X0 X1 sF3 X3
       grind)
    | exact superpose eq795 eq3905
    | exact resolve eq3905 eq795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq795 eq3905
  have eq77240 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 X1))) (M.op X0 X1)) (M.op (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 X1))) (k X3 X3))) = X3 := by
    intro X0 X1 X3
    first
    | exact superpose eq34051 eq77180
    | (have j0 := eq77180 X0 X1 (σ x) X3
       grind)
    | exact resolve eq77180 eq34051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34051 eq77180
  have eq77775 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 X1))) (M.op X0 X1)) (M.op (M.op (σ y) (M.op X1 (M.op X0 X1))) (k X3 X3))) = X3 := by
    intro X0 X1 X3
    first
    | exact superpose eq50738 eq77240
    | exact resolve eq77240 eq50738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50738 eq77240
  have eq78044 : ∀ X0 X1 X3 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op X1 (M.op X0 X1))) (M.op X0 X1)) (M.op X1 (k X3 X3))) = X3 := by
    intro X0 X1 X3
    first
    | exact superpose eq50711 eq77775
    | exact resolve eq77775 eq50711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77775
  have eq78150 : ∀ X0 X1 X3 : G, (M.op (M.op X1 (M.op X0 X1)) (M.op X1 (k X3 X3))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq78044 X1 X0 X3
       have i₂ := eq1209 X0 X1 sF4
       grind)
    | exact superpose eq1209 eq78044
    | exact resolve eq78044 eq1209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209 eq78044
  have eq78623 : ∀ X0 : G, (M.op (M.op y (M.op x y)) (M.op y (k X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq78150 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq78150
    | (have j0 := eq78150 x y X0
       grind)
    | exact resolve eq78150 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78150
  have eq79096 : ∀ X0 : G, (M.op (k (M.op x y) (M.op x y)) (M.op y (k X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq75159 eq78623
    | exact resolve eq78623 eq75159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78623
  have eq79517 : ∀ X0 : G, (M.op y (k X0 X0)) = (M.op X0 (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq79096 eq31545
    | exact resolve eq31545 eq79096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31545 eq79096
  have eq89961 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq1895 eq621
    | exact resolve eq621 eq1895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621
  have eq89972 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq89961
       have r₂ := eq27
       grind)
    | exact resolve eq89961 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89961
  have eq89980 : (σ y) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq89972
       have i₂ := eq3298 sF2
       grind)
    | exact superpose eq3298 eq89972
    | exact resolve eq89972 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89972
  have eq89985 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq89980
       have i₂ := eq3298 x
       grind)
    | exact superpose eq3298 eq89980
    | exact resolve eq89980 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89980
  have eq90013 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq89985 eq3349
    | exact resolve eq3349 eq89985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89985
  have eq90090 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ y = (M.op y x) := by grind
  clear eq90013
  have eq90155 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq90090 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq90090
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq90090
       grind)
    | exact resolve eq13 eq90090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90187 : (k (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq90090 eq15578
    | exact resolve eq15578 eq90090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90194 : (σ y) = (k (σ x) (σ y)) ∨ y = (k x x) ∨ y = (M.op y x) := by grind
  clear eq90155
  have eq90201 : (σ y) = (k (σ x) (σ x)) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq90090 eq90187
    | exact resolve eq90187 eq90090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90090 eq90187
  have eq90266 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq90194 eq1895
    | exact resolve eq1895 eq90194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1895 eq90194
  have eq90275 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x x) ∨ y = (M.op y x) ∨ y = (k x x) := by grind
  clear eq90266
  have eq90282 : y = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) ∨ y = (k x x) := by
    first
    | (have i₁ := eq90275
       have i₂ := eq3298 x
       grind)
    | exact superpose eq3298 eq90275
    | exact resolve eq90275 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90275
  have eq90283 : y = (k x x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by grind
  clear eq90282
  have eq90314 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq3349 x
       have i₂ := eq90283
       grind)
    | exact superpose eq90283 eq3349
    | exact resolve eq3349 eq90283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90283
  have eq90390 : y = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq90314
  have eq90486 : (k x x) = (M.op y x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq15578 x y
       have i₂ := eq90390
       grind)
    | exact superpose eq90390 eq15578
    | exact resolve eq15578 eq90390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15578
  have eq90500 : y = (k x x) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq90390 eq90486
    | exact resolve eq90486 eq90390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90390 eq90486
  have eq90581 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq90500
       grind)
    | exact superpose eq90500 eq39
    | exact resolve eq39 eq90500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq90652 : (σ (M.op x y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq26628 x
       have i₂ := eq90500
       grind)
    | exact superpose eq90500 eq26628
    | exact resolve eq26628 eq90500
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26628 eq90500
  have eq90691 : (σ (M.op x y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq90652
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq90652
    | exact resolve eq90652 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90652
  have eq90749 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq90581
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq90581
    | exact resolve eq90581 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90581
  have eq90765 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq2063 eq90691
    | exact resolve eq90691 eq2063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2063 eq90691
  have eq90806 : (σ y) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq90749
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq90749
    | exact resolve eq90749 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq90749
  have eq90818 : (σ (M.op x y)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq90765
       have i₂ := eq3298 sF2
       grind)
    | exact superpose eq3298 eq90765
    | exact resolve eq90765 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90765
  have eq90861 : (σ (M.op x y)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq90818
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq90818
    | exact resolve eq90818 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90818
  have eq90892 : (σ (M.op x y)) = (M.op (σ x) (k (σ x) (σ x))) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq20 eq90861
    | exact resolve eq90861 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90861
  have eq90917 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq90806 eq90892
    | exact resolve eq90892 eq90806
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90806 eq90892
  have eq90925 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq26 eq90917
    | exact resolve eq90917 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90917
  have eq90930 : (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq90925
       have r₂ := eq27
       grind)
    | exact resolve eq90925 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90925
  have eq90931 : (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq90930 eq28
    | exact resolve eq28 eq90930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq90930
  have eq91101 : y = (M.op x y) := by
    first
    | exact superpose eq90931 eq31
    | exact resolve eq31 eq90931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91102 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq90931 eq14
    | exact resolve eq14 eq90931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91104 : ∀ X0 : G, (k (σ X0) (σ y)) = (σ (k X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq90931 eq38
    | exact resolve eq38 eq90931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq90931
  have eq91155 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq91101
       grind)
    | exact superpose eq91101 eq18
    | exact resolve eq18 eq91101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq91206 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) = (M.op (M.op x y) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq8734 X0
       have i₂ := eq91101
       grind)
    | exact superpose eq91101 eq8734
    | exact resolve eq8734 eq91101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8734
  have eq91233 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (k (M.op x y) (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq28209 X0
       have i₂ := eq91101
       grind)
    | exact superpose eq91101 eq28209
    | exact resolve eq28209 eq91101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28209
  have eq91251 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (σ y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53926 X1 X0
       have i₂ := eq91101
       grind)
    | exact superpose eq91101 eq53926
    | exact resolve eq53926 eq91101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53926
  have eq102579 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (k (M.op X2 X1) (M.op X2 X1)) (k X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1094 (k (M.op X2 X1) (M.op X2 X1)) (k X0 X0) X1 X2
       have i₂ := eq3461 (M.op X2 X1) X0
       grind)
    | exact superpose eq3461 eq1094
    | exact resolve eq1094 eq3461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3461
  have eq102753 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 (M.op x y)) (M.op X0 X1)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1)))) = (M.op y (k (M.op (M.op X2 (M.op x y)) (M.op X0 X1)) (M.op (M.op X2 (M.op x y)) (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq79517 (M.op (M.op x sF0) (M.op X0 X1))
       have i₂ := eq1094 X0 X1 sF0 x
       grind)
    | exact superpose eq1094 eq79517
    | exact resolve eq79517 eq1094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79517
  have eq102833 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 (M.op x y)) (M.op X0 X1)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1)))) = (M.op y (M.op (M.op X0 X1) (M.op (M.op X2 (M.op x y)) (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq102753 X0 X1 X2
       have i₂ := eq798 (M.op X0 X1) (M.op X2 sF0)
       grind)
    | exact superpose eq798 eq102753
    | exact resolve eq102753 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102753
  have eq102911 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (σ y) (k (M.op X2 X1) (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq40479 eq102579
    | exact resolve eq102579 eq40479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40479 eq102579
  have eq103066 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X2 (M.op x y)) (M.op X0 X1)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1)))) = (M.op y (M.op X1 (M.op (M.op X2 (M.op x y)) (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq102833 X1 X2 X2
       have i₂ := eq77064 (M.op X2 sF0) X1 X2
       grind)
    | exact superpose eq77064 eq102833
    | exact resolve eq102833 eq77064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77064 eq102833
  have eq103116 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op x y) (k (M.op X2 X1) (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq91251 eq102911
    | exact resolve eq102911 eq91251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102911
  have eq103198 : ∀ X0 X1 : G, (M.op (M.op (k (M.op x y) (M.op x y)) (M.op X0 X1)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1)))) = (M.op y (M.op X1 (M.op (k (M.op x y) (M.op x y)) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | exact superpose eq75159 eq103066
    | exact resolve eq103066 eq75159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75159 eq103066
  have eq103225 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op (M.op (M.op x y) (M.op X1 (M.op X2 X1))) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq103116 X0 X1 X2
       have i₂ := eq798 X1 X2
       grind)
    | exact superpose eq798 eq103116
    | exact resolve eq103116 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103116
  have eq103278 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X1)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1)))) = (M.op y (M.op X1 (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | exact superpose eq91233 eq103198
    | exact resolve eq103198 eq91233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91233 eq103198
  have eq103314 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X1)) (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1)))) = (M.op (M.op x y) (M.op X1 (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq103278 X0 X1
       have i₂ := eq91101
       grind)
    | exact superpose eq91101 eq103278
    | exact resolve eq103278 eq91101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103278
  have eq103338 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op x y) (M.op X1 (M.op (M.op x y) (M.op X0 X1)))) := by
    intro X0 X1
    first
    | exact superpose eq10690 eq103314
    | exact resolve eq103314 eq10690
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10690 eq103314
  have eq125489 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) X0) X3) = (M.op (M.op (M.op x y) X0) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq103225 X3 (M.op (M.op X1 X2) X0) X2
       have i₂ := eq15480 X2 X1 X0 (M.op X1 X2)
       grind)
    | exact superpose eq15480 eq103225
    | exact resolve eq103225 eq15480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq125499 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq2268 eq103225
    | exact resolve eq103225 eq2268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2268
  have eq125520 : ∀ X0 X1 : G, (M.op (k X0 X0) X1) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq103225 X1 (k X0 X0) X0
       have i₂ := eq3342 X0
       grind)
    | exact superpose eq3342 eq103225
    | exact resolve eq103225 eq3342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3342
  have eq128696 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) X1) = (M.op (M.op (M.op x y) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq41972 eq125499
    | exact resolve eq125499 eq41972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq128726 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) X3) = (M.op (M.op (M.op x y) (M.op (M.op X2 (M.op (σ x) (σ y))) (M.op X0 X1))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq125499 (M.op (M.op X3 sF4) (M.op X0 X1)) X1
       have i₂ := eq1094 X0 X1 sF4 X3
       grind)
    | exact superpose eq1094 eq125499
    | exact resolve eq125499 eq1094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1094 eq125499
  have eq129504 : ∀ X0 X1 X3 : G, (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X1))) X3) = (M.op (M.op (M.op x y) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X1))) X3) := by
    intro X0 X1 X3
    first
    | exact superpose eq50839 eq128726
    | exact resolve eq128726 eq50839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50839 eq128726
  have eq129519 : ∀ X0 X1 : G, (M.op (M.op (σ y) (M.op (M.op x y) X0)) X1) = (M.op (M.op (M.op x y) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq54160 eq128696
    | exact resolve eq128696 eq54160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128696
  have eq129649 : ∀ X0 X1 X3 : G, (M.op (M.op (σ y) (M.op (M.op x y) (M.op X0 X1))) X3) = (M.op (M.op (M.op x y) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X1))) X3) := by
    intro X0 X1 X3
    first
    | exact superpose eq54160 eq129504
    | exact resolve eq129504 eq54160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54160 eq129504
  have eq129653 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) X1) = (M.op (M.op (M.op x y) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) X1) := by
    intro X0 X1
    first
    | exact superpose eq91251 eq129519
    | exact resolve eq129519 eq91251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91251 eq129519
  have eq129720 : ∀ X0 X1 X3 : G, (M.op X1 X3) = (M.op (M.op (M.op x y) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X1))) X3) := by
    intro X0 X1 X3
    first
    | exact superpose eq50711 eq129649
    | exact resolve eq129649 eq50711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50711 eq129649
  have eq129748 : ∀ X0 X1 X3 : G, (M.op X1 X3) = (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X1))) X3) := by
    intro X0 X1 X3
    first
    | exact superpose eq129653 eq129720
    | exact resolve eq129720 eq129653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129653 eq129720
  have eq142449 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X1) X3) = (M.op (M.op (M.op x y) X1) X3) := by
    intro X0 X1 X3
    first
    | exact superpose eq103225 eq125489
    | exact resolve eq125489 eq103225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103225 eq125489
  have eq144229 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X3 X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq142449 X0 X1 X3
       have i₂ := eq142449 sF0 X1 X3
       grind)
    | exact superpose eq142449 eq142449
    | exact resolve eq142449 eq142449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq144842 : ∀ X0 X1 X2 : G, (M.op (k X1 X1) X2) = (M.op (M.op X0 X1) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq125520 X1 x
       have i₂ := eq142449 sF0 X1 x
       grind)
    | exact superpose eq142449 eq125520
    | exact resolve eq125520 eq142449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125520
  have eq146936 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) X4) = (M.op (M.op X1 (M.op (M.op X2 X3) X0)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq144229 X1 (M.op (M.op X2 X3) X0) X4 X3
       have i₂ := eq15474 X3 X2 X0
       grind)
    | (have i₁ := eq144229 X0 (M.op (M.op (σ x) (σ y)) X2) X2 (σ y)
       have i₂ := eq15474 X0 X1 X2
       grind)
    | exact superpose eq15474 eq144229
    | exact resolve eq144229 eq15474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15474
  have eq147265 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op (σ x) (σ y)) X0)) X2) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq91206 eq144229
    | exact resolve eq144229 eq91206
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91206
  have eq147301 : ∀ X0 X1 X2 : G, (M.op (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) X2) = (M.op (M.op X1 (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq41972 eq144229
    | exact resolve eq144229 eq41972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41972
  have eq148954 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) (M.op (M.op (σ x) (σ y)) X0)) X2) = (M.op (M.op X1 (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq147301 X0 X1 x
       have i₂ := eq142449 sF3 (M.op sF4 X0) x
       grind)
    | exact superpose eq142449 eq147301
    | exact resolve eq147301 eq142449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147301
  have eq149061 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X3) X0)) X4) = (M.op (M.op (M.op x y) (M.op (M.op (σ x) (σ y)) X0)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq146936 X0 X1 X2 X3 X3
       have i₂ := eq142449 sF3 (M.op sF4 X0) X3
       grind)
    | exact superpose eq142449 eq146936
    | exact resolve eq146936 eq142449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146936
  have eq149473 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) X2) = (M.op (M.op X1 (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) X0)) X2) := by
    intro X0 X1 X2
    first
    | exact superpose eq147265 eq148954
    | exact resolve eq148954 eq147265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148954
  have eq149504 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X3) X0)) X4) = (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq147265 eq149061
    | exact resolve eq149061 eq147265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq147265 eq149061
  have eq180518 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op (M.op X2 (M.op (M.op x y) (M.op X3 X0))) X1) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq129748 eq144229
    | exact resolve eq144229 eq129748
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129748
  have eq218779 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op (M.op X1 (k X0 X0)) (M.op (M.op x y) X0))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq3462 eq103338
    | exact resolve eq103338 eq3462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3462 eq103338
  have eq283027 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 (M.op X0 X1))) X4) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X1))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq144229 X2 (M.op X3 (M.op X0 X1)) X4 (M.op (M.op x x) (M.op X3 X3))
       have i₂ := eq1099 X0 X1 x x X3
       grind)
    | exact superpose eq1099 eq144229
    | exact resolve eq144229 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq283060 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 (M.op X3 (M.op X0 X1))) X4) = (M.op (M.op (M.op x y) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X0 X1))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq283027 X0 X1 X2 X3 X3
       have i₂ := eq142449 sF4 (M.op (k sF4 sF4) (M.op X0 X1)) X3
       grind)
    | exact superpose eq142449 eq283027
    | exact resolve eq283027 eq142449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283027
  have eq284326 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X1))) X4) = (M.op (M.op X2 (M.op X3 (M.op X0 X1))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq149473 eq283060
    | exact resolve eq283060 eq149473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq283060
  have eq285364 : ∀ X0 X1 X2 X3 X4 : G, (M.op X1 X4) = (M.op (M.op X2 (M.op X3 (M.op X0 X1))) X4) := by
    intro X0 X1 X2 X3 X4
    first
    | exact superpose eq180518 eq284326
    | exact resolve eq284326 eq180518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284326
  have eq288641 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X2 X3))) (M.op X0 X0)) = (M.op (M.op X1 (M.op (M.op (M.op (σ x) (σ y)) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X2 X3))) (M.op X0 X0))) (M.op (M.op X2 X3) X0)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq1100 eq15480
    | exact resolve eq15480 eq1100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1100
  have eq288950 : ∀ X0 X2 X3 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X2 X3))) (M.op X0 X0)) = (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op X0 X0))) (M.op (M.op X2 X3) X0)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq288641 X0 x X2 X3
       have i₂ := eq149504 (M.op X0 X0) x sF4 (M.op (k sF4 sF4) (M.op X2 X3)) (M.op (M.op X2 X3) X0)
       grind)
    | exact superpose eq149504 eq288641
    | exact resolve eq288641 eq149504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149504 eq288641
  have eq289920 : ∀ X0 X2 X3 : G, (M.op X0 (M.op (M.op X2 X3) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X2 X3))) (M.op X0 X0)) := by
    intro X0 X2 X3
    first
    | exact superpose eq180518 eq288950
    | exact resolve eq288950 eq180518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq288950
  have eq290805 : ∀ X0 X2 X3 : G, (M.op X0 (M.op (M.op X2 X3) X0)) = (M.op (M.op (M.op x y) (M.op (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (M.op X2 X3))) (M.op X0 X0)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq289920 X0 X2 X3
       have i₂ := eq142449 sF4 (M.op (k sF4 sF4) (M.op X2 X3)) (M.op X0 X0)
       grind)
    | exact superpose eq142449 eq289920
    | exact resolve eq289920 eq142449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142449 eq289920
  have eq291002 : ∀ X0 X2 X3 : G, (M.op X0 (M.op (M.op X2 X3) X0)) = (M.op (M.op (M.op x y) (M.op (M.op x y) (M.op X2 X3))) (M.op X0 X0)) := by
    intro X0 X2 X3
    first
    | exact superpose eq149473 eq290805
    | exact resolve eq290805 eq149473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq149473 eq290805
  have eq291131 : ∀ X0 X2 X3 : G, (M.op X3 (M.op X0 X0)) = (M.op X0 (M.op (M.op X2 X3) X0)) := by
    intro X0 X2 X3
    first
    | exact superpose eq180518 eq291002
    | exact resolve eq291002 eq180518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180518 eq291002
  have eq291198 : ∀ X0 X2 X3 : G, (M.op X3 (k X0 X0)) = (M.op X0 (M.op (M.op X2 X3) X0)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq291131 X0 X2 X3
       have i₂ := eq3298 X0
       grind)
    | exact superpose eq3298 eq291131
    | exact resolve eq291131 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291131
  have eq292447 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (k (M.op X1 X2) (M.op X1 X2))) = (M.op (M.op X3 X2) (M.op (M.op X4 X0) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq144229 X3 X2 (M.op (M.op X4 X0) (M.op X1 X2)) X1
       have i₂ := eq291198 (M.op X1 X2) X4 X0
       grind)
    | exact superpose eq291198 eq144229
    | exact resolve eq144229 eq291198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144229
  have eq292759 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X2 (M.op X1 X2))) = (M.op (M.op X3 X2) (M.op (M.op X4 X0) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq292447 X0 X1 X2 X3 X4
       have i₂ := eq798 X2 X1
       grind)
    | exact superpose eq798 eq292447
    | exact resolve eq292447 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798 eq292447
  have eq297224 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X2 X1) (M.op (M.op X3 (M.op X4 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq15480 (M.op X3 (M.op X4 X0)) x X1 X2
       have i₂ := eq285364 X4 X0 x X3 X1
       grind)
    | exact superpose eq285364 eq15480
    | exact resolve eq15480 eq285364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15480 eq285364
  have eq297978 : ∀ X0 X1 X4 : G, (M.op (M.op X4 X0) (M.op X1 (M.op X0 X1))) = X1 := by
    intro X0 X1 X4
    first
    | (have i₁ := eq297224 X0 X1 x x X4
       have i₂ := eq292759 (M.op X4 X0) X0 X1 x x
       grind)
    | exact superpose eq292759 eq297224
    | exact resolve eq297224 eq292759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292759 eq297224
  have eq299684 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) (M.op (M.op x y) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq91155 eq297978
    | exact resolve eq297978 eq91155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91155 eq297978
  have eq300618 : (M.op x y) = (M.op (k x x) (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq299684 x
       have i₂ := eq144842 x x (M.op sF0 sF0)
       grind)
    | exact superpose eq144842 eq299684
    | exact resolve eq299684 eq144842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq144842 eq299684
  have eq301366 : (M.op x y) = (M.op (k x x) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq300618
       have i₂ := eq3298 sF0
       grind)
    | exact superpose eq3298 eq300618
    | exact resolve eq300618 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq300618
  have eq826189 : (τ (σ y)) = (k x x) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq90201 eq97
    | exact resolve eq97 eq90201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq90201
  have eq826689 : y = (k x x) ∨ y = (k x x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq31 eq826189
    | exact resolve eq826189 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq826189
  have eq826690 : y = (k x x) ∨ y = (M.op y x) := by grind
  clear eq826689
  have eq826925 : (M.op x y) = (k x x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq826690
       have i₂ := eq91101
       grind)
    | exact superpose eq91101 eq826690
    | exact resolve eq826690 eq91101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826690
  have eq827113 : (M.op x y) = (k x x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq826925
       have i₂ := eq91101
       grind)
    | exact superpose eq91101 eq826925
    | exact resolve eq826925 eq91101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91101 eq826925
  have eq827465 : (M.op x y) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq3349 x
       have i₂ := eq827113
       grind)
    | exact superpose eq827113 eq3349
    | exact resolve eq3349 eq827113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3349 eq827113
  have eq827688 : (M.op x y) = (M.op (M.op x y) x) := by grind
  clear eq827465
  have eq827950 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op X0 (k x x)) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq827688 eq218779
    | exact resolve eq218779 eq827688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218779
  have eq827972 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k x (M.op x y)) := by
    first
    | exact superpose eq827688 eq13
    | (have r₁ := eq13 x (M.op x y)
       have r₂ := eq827688
       grind)
    | exact resolve eq13 eq827688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827688
  have eq828142 : (M.op x y) = (k x (M.op x y)) := by grind
  clear eq827972
  have eq828274 : x = (M.op (k x x) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq827950 x
       have i₂ := eq291198 sF0 x (k x x)
       grind)
    | exact superpose eq291198 eq827950
    | exact resolve eq827950 eq291198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291198 eq827950
  have eq828431 : x = (M.op x y) := by
    first
    | exact superpose eq301366 eq828274
    | exact resolve eq828274 eq301366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301366 eq828274
  have eq828709 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq828431
       grind)
    | exact superpose eq828431 eq22
    | exact resolve eq22 eq828431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828431
  have eq828974 : (σ x) = (σ y) := by
    first
    | exact superpose eq828709 eq91102
    | exact resolve eq91102 eq828709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91102 eq828709
  have eq829737 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq828974 eq26
    | exact resolve eq26 eq828974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq830299 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq829737
       have i₂ := eq3298 sF2
       grind)
    | exact superpose eq3298 eq829737
    | exact resolve eq829737 eq3298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3298 eq829737
  have eq830863 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq828142 eq91104
    | exact resolve eq91104 eq828142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91104 eq828142
  have eq830873 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq828974 eq830863
    | exact resolve eq830863 eq828974
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq828974 eq830863
  have eq830881 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq830873
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq830873
    | exact resolve eq830873 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq830873
  have eq830887 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq830299 eq830881
    | exact resolve eq830881 eq830299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830299 eq830881
  have eq830891 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq830887
    | exact resolve eq830887 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq830887
  have eq830894 : False := by grind
  exact eq830894

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pxx_pyy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  clear eq43
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : x ≠ (M.op x y) ∨ (M.op y y) = (k y x) := by
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
  have eq64 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op (M.op (M.op X2 X1) (M.op X0 X0)) (M.op (M.op X2 X1) (M.op X0 X0))) = (k (M.op (M.op X2 X1) (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq13 (M.op (M.op X2 X0) (M.op X0 X0)) X0
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq87
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq87
    | exact resolve eq87 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq93
    | exact resolve eq93 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
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
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq95
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq95
    | exact resolve eq95 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq101 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq108 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq108 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq108 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq111 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq109 (σ X0)
       grind)
    | exact superpose eq109 eq10
    | exact resolve eq10 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq109 y
       grind)
    | exact superpose eq109 eq73
    | exact resolve eq73 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq114 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq109 sF2
       grind)
    | exact superpose eq109 eq49
    | exact resolve eq49 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq115 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq114
       have i₂ := eq109 x
       grind)
    | exact superpose eq109 eq114
    | exact resolve eq114 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq113
       have i₂ := eq109 sF3
       grind)
    | exact superpose eq109 eq113
    | exact resolve eq113 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq118 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq111 X0
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq111
    | exact resolve eq111 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq125 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq101
       have i₂ := eq109 sF3
       grind)
    | exact superpose eq109 eq101
    | exact resolve eq101 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq126 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq125
       have i₂ := eq109 y
       grind)
    | exact superpose eq109 eq125
    | exact resolve eq125 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq251 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq50 (M.op sF0 sF0)
       have i₂ := eq14 sF0 sF0 sF0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op y (M.op x y)))) := by
    first
    | exact superpose eq251 eq50
    | exact resolve eq50 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq360 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq109 (τ X0)
       grind)
    | exact superpose eq109 eq34
    | exact resolve eq34 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq371 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq360 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq360
    | exact resolve eq360 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq360
  have eq374 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq371 X0
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq371
    | exact resolve eq371 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq371
  have eq553 : ∀ X0 X1 : G, (M.op (σ X0) (M.op (σ (M.op X0 X0)) (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0) (σ X0)
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq14
    | exact resolve eq14 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : ∀ X0 X1 X2 : G, (σ X0) = (M.op X1 (M.op (M.op X2 X1) (σ (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (σ X0) X1 X2
       have i₂ := eq118 X0
       grind)
    | exact superpose eq118 eq14
    | exact resolve eq14 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq583 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op y (M.op (M.op x y) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq50
    | exact resolve eq50 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq623 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq52 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq654 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X1 X1) X1 X2 X1
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq659 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq52 X0 x x X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq666 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq667 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) X2 X3
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq668 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq667 X0 X1 X2 X3
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq667
    | exact resolve eq667 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq667
  have eq669 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq666 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq666
    | exact resolve eq666 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq756 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op (M.op X2 X1) (M.op X0 X0)) X1) = (M.op (M.op X0 X0) (M.op (M.op X2 X1) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X0 X1 X2
       have i₂ := eq53 (M.op X2 X1) (M.op X0 X0)
       grind)
    | exact superpose eq53 eq65
    | (have j0 := eq65 X0 X1 X2
       grind)
    | (have r₁ := eq65 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X1 (M.op X0 X1)) X2
       have r₂ := eq53 X0 X1
       grind)
    | (have r₁ := eq65 (M.op X1 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1)) X2
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq65 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq824 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq374 X0
       grind)
    | exact superpose eq374 eq16
    | exact resolve eq16 eq374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq846 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X1 X1)) X1) = (M.op (M.op X1 X1) (M.op (M.op X0 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq756 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq1092 : ∀ X0 : G, (τ X0) = (M.op y (M.op (M.op x y) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq824 X0
       grind)
    | exact superpose eq824 eq50
    | exact resolve eq50 eq824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq824
  have eq1268 : (M.op (M.op x y) (M.op (M.op x y) (M.op x y))) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq253 eq50
    | exact resolve eq50 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq1283 : (M.op (M.op x y) (M.op y (M.op x y))) = (M.op y (M.op y (M.op x y))) := by
    first
    | exact superpose eq251 eq1268
    | exact resolve eq1268 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1268
  have eq1827 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq623 X0 X0 X0
       grind)
    | exact superpose eq623 eq14
    | exact resolve eq14 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1828 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (M.op X0 (M.op X0 X0))
       have i₂ := eq623 X0 X0 X0
       grind)
    | exact superpose eq623 eq50
    | exact resolve eq50 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1829 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq623 X0 X0 X0
       grind)
    | exact superpose eq623 eq51
    | exact resolve eq51 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq1841 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    have f1841_12 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
      intro X0 X1
      grind
    have f1841_13 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X1 (M.op X2 X2))) = X2 := by
      intro X0 X1 X2
      grind
    have f1841_22 : X0 ≠ (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) := by grind
    have f1841_89 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
      intro X0 X1
      first
      | (have i₁ := f1841_12 (M.op x (M.op x x)) X1
         have i₂ := f1841_13 x x x
         grind)
      | exact superpose f1841_13 f1841_12
      | exact resolve f1841_12 f1841_13
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1841_115 : X0 ≠ X0 := by
      first
      | (have i₁ := f1841_22
         have i₂ := f1841_89 X0 X1
         grind)
      | exact superpose f1841_89 f1841_22
      | (have r₁ := f1841_22
         have r₂ := f1841_89 X0 X1
         grind)
      | exact resolve f1841_22 f1841_89
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1841_118 : False := by grind
    exact f1841_118
  clear eq659
  have eq1906 : (M.op x y) = (M.op y (M.op y (M.op y (M.op x y)))) := by
    first
    | exact superpose eq1283 eq259
    | exact resolve eq259 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259 eq1283
  have eq2123 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq583 X0
       have i₂ := eq1828 X0
       grind)
    | exact superpose eq1828 eq583
    | exact resolve eq583 eq1828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2150 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1828 eq588
    | exact resolve eq588 eq1828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1828
  have eq2161 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq588 eq2150
    | exact resolve eq2150 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2150
  have eq2198 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq50 eq2123
    | exact resolve eq2123 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq2123
  have eq2251 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq2198 X0
       grind)
    | exact superpose eq2198 eq13
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X0)
       have r₂ := eq2198 X0
       grind)
    | exact resolve eq13 eq2198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2198
  have eq2271 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq2251 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2251
  have eq2430 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq2271 (M.op x (M.op x x))
       have i₂ := eq623 x x x
       grind)
    | exact superpose eq623 eq2271
    | exact resolve eq2271 eq623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq2819 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1829 eq588
    | exact resolve eq588 eq1829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1829
  have eq2830 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq588 eq2819
    | exact resolve eq2819 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588 eq2819
  have eq3240 : y = (M.op (M.op x y) (M.op y (M.op y y))) := by
    first
    | (have i₁ := eq1841 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1841
    | (have j0 := eq1841 y x
       grind)
    | exact resolve eq1841 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5967 : ∀ X0 X1 X2 X3 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq668 X0 X1 X2 X3
       have i₂ := eq669 X0 X1
       grind)
    | exact superpose eq669 eq668
    | exact resolve eq668 eq669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668 eq669
  have eq6049 : ∀ X0 X1 X2 : G, (M.op y (M.op (M.op x y) X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5967 X0 (M.op X0 (M.op X0 X0)) X2 x
       have i₂ := eq583 X0
       grind)
    | exact superpose eq583 eq5967
    | exact resolve eq5967 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5967
  have eq6621 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq654 (M.op X0 X0) X1 X2
       have i₂ := eq846 X0 X0
       grind)
    | exact superpose eq846 eq654
    | exact resolve eq654 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654 eq846
  have eq6679 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (k (M.op X0 (M.op X0 X0)) X0)) (k (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6621 X1 X1 X2
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq6621
    | exact resolve eq6621 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq6621
  have eq6767 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6679 X0 X1 X2
       have i₂ := eq2430 X0
       grind)
    | exact superpose eq2430 eq6679
    | exact resolve eq6679 eq2430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2430 eq6679
  have eq6918 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq6767 X1 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq583 X0
       grind)
    | exact superpose eq583 eq6767
    | exact resolve eq6767 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq583 eq6767
  have eq18995 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq96 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18996 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq18995
    | exact resolve eq18995 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18995
  have eq19001 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18996
       have r₂ := eq27
       grind)
    | exact resolve eq18996 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18996
  have eq19003 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq19001
    | exact resolve eq19001 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19001
  have eq19005 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq19003
    | exact resolve eq19003 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19003
  have eq19008 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19005 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq19005
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq19005
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq19005
       grind)
    | exact resolve eq12 eq19005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19005
  have eq19050 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq19008
       have r₂ := eq26
       grind)
    | exact resolve eq19008 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19008
  have eq19053 : (σ x) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq19050
    | exact resolve eq19050 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19050
  have eq19054 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq19053
  have eq19166 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19054 eq96
    | exact resolve eq96 eq19054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq19054
  have eq19171 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq19166
  have eq19178 : (τ (σ (M.op x y))) = (M.op x x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19171 eq115
    | exact resolve eq115 eq19171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq19209 : (τ (σ x)) = (M.op y (M.op (M.op x y) (τ (σ (M.op x y))))) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19171 eq1092
    | exact resolve eq1092 eq19171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092 eq19171
  have eq19266 : (τ (σ x)) = (M.op y (M.op (M.op x y) (M.op x y))) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq19209
    | exact resolve eq19209 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19209
  have eq19271 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq30 eq19178
    | exact resolve eq19178 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq19178
  have eq19272 : (τ (σ x)) = (M.op y (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq251 eq19266
    | exact resolve eq19266 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251 eq19266
  have eq19276 : x = (M.op y (M.op y (M.op x y))) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28 eq19272
    | exact resolve eq19272 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19272
  have eq20344 : (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq19276 eq1906
    | exact resolve eq1906 eq19276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1906 eq19276
  have eq20381 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20344
  have eq20540 : x = (M.op (M.op x y) (M.op x (M.op x x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1841 x y
       have i₂ := eq20381
       grind)
    | exact superpose eq20381 eq1841
    | exact resolve eq1841 eq20381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1841
  have eq20977 : (M.op x x) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20540 eq589
    | exact resolve eq589 eq20540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589 eq20540
  have eq21051 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19271
       have i₂ := eq20977
       grind)
    | exact superpose eq20977 eq19271
    | exact resolve eq19271 eq20977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19271 eq20977
  have eq21087 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq21051
  have eq22473 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x y)) (M.op X0 X0))) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq553 x X0
       have i₂ := eq21087
       grind)
    | exact superpose eq21087 eq553
    | exact resolve eq553 eq21087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553 eq21087
  have eq22577 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x y)) (M.op X0 X0))) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq20 eq22473
    | (have j0 := eq22473 X0
       grind)
    | exact resolve eq22473 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22473
  have eq22619 : ∀ X0 : G, (M.op (σ x) (M.op (σ (M.op x y)) (M.op X0 X0))) = X0 ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq22577 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22577
    | (have j0 := eq22577 X0
       grind)
    | exact resolve eq22577 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22577
  have eq22751 : ∀ X0 : G, (σ X0) = (M.op x (M.op (M.op x y) (σ (M.op X0 X0)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq556 X0 x y
       have i₂ := eq20381
       grind)
    | exact superpose eq20381 eq556
    | exact resolve eq556 eq20381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq30262 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op x (M.op (M.op x y) X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1827 X0 x y
       have i₂ := eq20381
       grind)
    | exact superpose eq20381 eq1827
    | exact resolve eq1827 eq20381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1827
  have eq32234 : ∀ X0 : G, (M.op y (M.op (M.op x y) X0)) = (M.op x (M.op (M.op x y) X0)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6049 X0 x y
       have i₂ := eq20381
       grind)
    | exact superpose eq20381 eq6049
    | exact resolve eq6049 eq20381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6049 eq20381
  have eq54310 : (σ (M.op x y)) = (M.op (σ x) (M.op x (M.op (M.op x y) (σ (M.op x y))))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22619 sF1
       have i₂ := eq30262 sF1
       grind)
    | exact superpose eq30262 eq22619
    | exact resolve eq22619 eq30262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22619 eq30262
  have eq54379 : (σ (M.op x y)) = (M.op (σ x) (M.op x (M.op (M.op x y) (σ (M.op x y))))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq54310
  have eq56336 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3240 eq32234
    | exact resolve eq32234 eq3240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3240 eq32234
  have eq56545 : (M.op x y) = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56336
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq56336
    | exact resolve eq56336 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56336
  have eq56656 : (σ y) = (M.op x (M.op (M.op x y) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq22751 y
       have i₂ := eq56545
       grind)
    | exact superpose eq56545 eq22751
    | exact resolve eq22751 eq56545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22751 eq56545
  have eq56707 : (σ y) = (M.op x (M.op (M.op x y) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq56656
  have eq56735 : (σ y) = (M.op x (M.op (M.op x y) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq56707
    | exact resolve eq56707 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56707
  have eq56791 : (σ y) = (M.op x (M.op (M.op x y) (σ (M.op x y)))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq56735
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq56735
    | exact resolve eq56735 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq56735
  have eq59277 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq56791 eq54379
    | exact resolve eq54379 eq56791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54379 eq56791
  have eq59330 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq59277
  have eq59346 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq59330
    | exact resolve eq59330 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59330
  have eq59347 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq59346
       have r₂ := eq27
       grind)
    | exact resolve eq59346 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59346
  have eq59350 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq59347 eq64
    | (have r₁ := eq64
       have r₂ := eq59347
       grind)
    | exact resolve eq64 eq59347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq59393 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq59347 eq2830
    | exact resolve eq2830 eq59347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2830
  have eq59406 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq59350
  have eq59408 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq59393
    | exact resolve eq59393 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59393
  have eq59496 : (M.op (σ x) (σ y)) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq59408 eq2271
    | exact resolve eq2271 eq59408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2271 eq59408
  have eq59644 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq59347 eq59496
    | exact resolve eq59496 eq59347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59347 eq59496
  have eq59651 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq59644
  have eq59660 : (τ (σ x)) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq59651 eq92
    | exact resolve eq92 eq59651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59651
  have eq59677 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq59660
    | exact resolve eq59660 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq59660
  have eq61727 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq59406 eq92
    | exact resolve eq92 eq59406
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq59406
  have eq61747 : (M.op y y) = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq126 eq61727
    | exact resolve eq61727 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126 eq61727
  have eq61751 : (M.op y y) = (k y x) := by
    first
    | (have r₁ := eq61747
       have r₂ := eq63
       grind)
    | exact resolve eq61747 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq61747
  have eq61752 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq61751
       have i₂ := eq59677
       grind)
    | exact superpose eq59677 eq61751
    | exact resolve eq61751 eq59677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59677 eq61751
  have eq62170 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6918 y y
       have i₂ := eq61752
       grind)
    | exact superpose eq61752 eq6918
    | exact resolve eq6918 eq61752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61752
  have eq62204 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq62170
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq62170
    | exact resolve eq62170 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62170
  have eq62205 : x = (M.op x y) := by grind
  clear eq62204
  have eq62289 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq62205 eq20
    | exact resolve eq20 eq62205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq62386 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq62205 eq2161
    | exact resolve eq2161 eq62205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2161
  have eq62418 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq62386
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq62386
    | exact resolve eq62386 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq62386
  have eq62477 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq62289
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq62289
    | exact resolve eq62289 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62289
  have eq62478 : x = (M.op y y) := by
    first
    | exact superpose eq62205 eq62418
    | exact resolve eq62418 eq62205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62205 eq62418
  have eq62524 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq62477 eq26
    | exact resolve eq26 eq62477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq62748 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq62478
       grind)
    | exact superpose eq62478 eq116
    | exact resolve eq116 eq62478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq62478
  have eq62982 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq62748
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq62748
    | exact resolve eq62748 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq62748
  have eq63016 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq62477 eq62982
    | exact resolve eq62982 eq62477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62477 eq62982
  have eq63254 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq63016 eq6918
    | exact resolve eq6918 eq63016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6918 eq63016
  have eq63267 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq62524 eq63254
    | exact resolve eq63254 eq62524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62524 eq63254
  have eq63331 : False := by grind
  exact eq63331

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyx_pyx_pxx_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq32 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq32
    | exact resolve eq32 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq32 X0 X0
       grind)
    | exact superpose eq32 eq9
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) X2 X3
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq9
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq32 X0 (M.op X0 (M.op X0 X0))
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq32
    | exact resolve eq32 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq9
    | exact resolve eq9 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq34 X1 (M.op (M.op x x) (M.op X0 X0)) x
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq34
    | exact resolve eq34 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq75 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       grind)
    | exact resolve eq13 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq43 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq43
    | exact resolve eq43 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X0 X0)) (M.op X0 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 (M.op X0 X0)) (M.op X1 (M.op X1 X1))
       have i₂ := eq43 X1 X0
       grind)
    | exact superpose eq43 eq9
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq9
    | exact resolve eq9 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 (M.op X1 (M.op X1 X1))
       have i₂ := eq43 X1 X1
       grind)
    | exact superpose eq43 eq57
    | exact resolve eq57 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq163 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op (M.op X0 (M.op X0 X0)) (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq115 (M.op X0 (M.op X0 X0)) X1 X2
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq115
    | exact resolve eq115 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq173 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X2 X2)) (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq115 X2 X1 (M.op X0 (M.op X0 X0))
       have i₂ := eq43 X0 X0
       grind)
    | exact superpose eq43 eq115
    | exact resolve eq115 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq222 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq248 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X0 (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq41 X2
       have i₂ := eq116 X2 X0 X1
       grind)
    | exact superpose eq116 eq41
    | exact resolve eq41 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq252 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X2) (M.op X0 (M.op (M.op X1 X0) X2))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq122 X2 X3
       have i₂ := eq116 X2 X0 X1
       grind)
    | exact superpose eq116 eq122
    | exact resolve eq122 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq263 : ∀ X0 X1 X2 X3 : G, (M.op X2 X3) = (M.op X3 (M.op X0 (M.op (M.op X1 X0) (M.op X2 X3)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 X3) X3 X2
       have i₂ := eq116 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq116 eq9
    | exact resolve eq9 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq405 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq222 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq222
    | (have j0 := eq222 (σ X0) (σ X1)
       grind)
    | exact resolve eq222 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1025 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq405 X1 X0
       have i₂ := eq222 X1 X0
       grind)
    | exact superpose eq222 eq405
    | (have j0 := eq405 X0 X1
       have j1 := eq222 (σ X0) (σ X1)
       grind)
    | exact resolve eq405 eq222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222 eq405
  have eq1063 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X2 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq39 X2 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq39
    | exact resolve eq39 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq1298 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq75 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq1345 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op (M.op X0 (M.op X0 X0)) (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq122 X1 X2
       have i₂ := eq100 X1 X0
       grind)
    | exact superpose eq100 eq122
    | exact resolve eq122 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq2123 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op (M.op X4 X0) (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq173 (M.op X1 (M.op (M.op X2 X1) X0)) X3 (M.op X4 X0)
       have i₂ := eq252 X1 X2 X0 X4
       grind)
    | exact superpose eq252 eq173
    | exact resolve eq173 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2338 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2123 X0 X1 X2 X3 X4
       have i₂ := eq32 X4 X0
       grind)
    | exact superpose eq32 eq2123
    | exact resolve eq2123 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2123
  have eq2403 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) (M.op (M.op (M.op X2 X1) X0) (M.op X1 (M.op (M.op X2 X1) X0)))) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2338 X0 X1 X2 X3 X4
       have i₂ := eq32 X1 (M.op (M.op X2 X1) X0)
       grind)
    | exact superpose eq32 eq2338
    | exact resolve eq2338 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2338
  have eq2433 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 (M.op (M.op X2 X1) X0)) X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq2403 X0 X1 X2 X3 X4
       have i₂ := eq252 X1 X2 X0 (M.op X2 X1)
       grind)
    | exact superpose eq252 eq2403
    | exact resolve eq2403 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq2403
  have eq2442 : ∀ X0 X3 X4 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 (M.op X4 X0))) X0) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq2433 X0 x x X3 X4
       have i₂ := eq248 x x X0
       grind)
    | exact superpose eq248 eq2433
    | exact resolve eq2433 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq2433
  have eq2472 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0)))) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2442 (M.op X1 X0) X2 (M.op x (M.op X1 X1))
       have i₂ := eq173 X0 x X1
       grind)
    | exact superpose eq173 eq2442
    | exact resolve eq2442 eq173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173 eq2442
  have eq2561 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2472 X0 X1 X2
       have i₂ := eq122 X0 X1
       grind)
    | exact superpose eq122 eq2472
    | exact resolve eq2472 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2472
  have eq2583 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X0)) = (M.op (M.op X2 X0) (M.op X1 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2561 X0 X1 X2
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq2561
    | exact resolve eq2561 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2561
  have eq2603 : ∀ X0 : G, (M.op (σ (τ X0)) (σ (τ X0))) = (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq17 X0 (τ X0)
       have i₂ := eq1298 (τ X0)
       grind)
    | exact superpose eq1298 eq17
    | (have j1 := eq1298 (τ X0)
       grind)
    | exact resolve eq17 eq1298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1298
  have eq2613 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq2603 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2603
    | (have j0 := eq2603 X0
       grind)
    | exact resolve eq2603 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2603
  have eq2617 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq2613 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2613
    | (have j0 := eq2613 X0
       grind)
    | exact resolve eq2613 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2613
  have eq2620 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2617 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq2617 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq2617 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2617
  have eq2628 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2620 (σ X0)
       grind)
    | exact superpose eq2620 eq15
    | exact resolve eq15 eq2620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2635 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2628 X0
       have i₂ := eq2620 X0
       grind)
    | exact superpose eq2620 eq2628
    | exact resolve eq2628 eq2620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2620 eq2628
  have eq6045 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq263 (M.op X1 X1) x X1 (M.op X0 X0)
       have i₂ := eq115 X1 x X0
       grind)
    | exact superpose eq115 eq263
    | exact resolve eq263 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq263
  have eq6225 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op (M.op X1 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6045 X0 X1
       have i₂ := eq2583 X0 (M.op X1 X1) X0
       grind)
    | exact superpose eq2583 eq6045
    | exact resolve eq6045 eq2583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2583 eq6045
  have eq6635 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1))) X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq163 X1 X2 X0
       have i₂ := eq6225 X0 (M.op X1 (M.op X1 X1))
       grind)
    | exact superpose eq6225 eq163
    | exact resolve eq163 eq6225
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163 eq6225
  have eq6827 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op (M.op (M.op X1 X1) (M.op X1 (M.op X1 X1))) X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6635 X0 X1 X2
       have i₂ := eq32 X1 (M.op X1 X1)
       grind)
    | exact superpose eq32 eq6635
    | exact resolve eq6635 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq6635
  have eq6913 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X1) (M.op X0 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6827 X0 X1 X2
       have i₂ := eq122 X1 X1
       grind)
    | exact superpose eq122 eq6827
    | exact resolve eq6827 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq6827
  have eq11813 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1025 x y
       grind)
    | exact superpose eq1025 eq16
    | (have j1 := eq1025 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq1025 x y
       grind)
    | exact resolve eq16 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025
  have eq11822 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq11813
  have eq16753 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X1)) = (M.op (M.op X1 (M.op X1 X1)) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1063 X1 X1 (M.op X0 X1)
       have i₂ := eq39 X1 X0 X1 X0
       grind)
    | exact superpose eq39 eq1063
    | exact resolve eq1063 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq1063
  have eq21094 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (M.op (σ y) (M.op (σ y) (σ y))) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1345 (σ y) (σ x) X0
       have i₂ := eq11822
       grind)
    | exact superpose eq11822 eq1345
    | exact resolve eq1345 eq11822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11822
  have eq21145 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (σ x)) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq21094 X0
       have i₂ := eq16753 (σ x) (σ y)
       grind)
    | exact superpose eq16753 eq21094
    | exact resolve eq21094 eq16753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21094
  have eq21161 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq21145 x
       have i₂ := eq6913 (σ y) (σ x) x
       grind)
    | exact superpose eq6913 eq21145
    | exact resolve eq21145 eq6913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21145
  have eq21165 : y = (τ (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq21161
       grind)
    | exact superpose eq21161 eq10
    | exact resolve eq10 eq21161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21161
  have eq21184 : (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq21165
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq21165
    | exact resolve eq21165 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21165
  have eq21224 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op (M.op y (M.op y y)) (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1345 y x X0
       have i₂ := eq21184
       grind)
    | exact superpose eq21184 eq1345
    | exact resolve eq1345 eq21184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1345 eq21184
  have eq21271 : ∀ X0 : G, x = (M.op (M.op X0 x) (M.op y (M.op x y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq21224 X0
       have i₂ := eq16753 x y
       grind)
    | exact superpose eq16753 eq21224
    | exact resolve eq21224 eq16753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16753 eq21224
  have eq21284 : x = y ∨ x = y := by
    first
    | (have i₁ := eq21271 x
       have i₂ := eq6913 y x x
       grind)
    | exact superpose eq6913 eq21271
    | exact resolve eq21271 eq6913
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6913 eq21271
  have eq21285 : x = y := by grind
  clear eq21284
  have eq21292 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21285
       grind)
    | exact superpose eq21285 eq16
    | exact resolve eq16 eq21285
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21285
  have eq21293 : False := by grind
  exact eq21293

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,X) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyx_x_pxx_y_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : x ≠ (M.op x y) ∨ (M.op y y) = (k y x) := by
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
  have eq64 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (M.op (M.op (M.op X2 X1) (M.op X0 X0)) (M.op (M.op X2 X1) (M.op X0 X0))) = (k (M.op (M.op X2 X1) (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq13 (M.op (M.op X2 X0) (M.op X0 X0)) X0
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  have eq72 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq73 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq75 : y ≠ (M.op x y) ∨ x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq95 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ X0) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ X0)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq102 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq102
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq111
    | exact resolve eq111 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq113 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq112
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq112
    | exact resolve eq112 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
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
  have eq125 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq37 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq37
    | exact resolve eq37 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (σ (k (M.op x y) y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq37 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq37
    | (have j0 := eq37 y
       grind)
    | exact resolve eq37 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq150 : (k (M.op x y) y) = (τ (k (σ (M.op x y)) (σ y))) := by
    first
    | exact superpose eq133 eq16
    | exact resolve eq16 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133
  have eq270 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k y (τ X0))
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq16
    | exact resolve eq16 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq34
  have eq316 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | exact superpose eq125 eq16
    | exact resolve eq16 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq622 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (M.op X1 X0)
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq677 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X1 X1) X1 X2 X1
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq52
    | exact resolve eq52 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq682 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq53 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq52 X0 x x X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq688 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op y (M.op (M.op x y) (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq50 (M.op (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1)))
       have i₂ := eq52 (M.op X0 X1) X0 X1 (M.op X0 X1)
       grind)
    | exact superpose eq52 eq50
    | exact resolve eq50 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq691 : ∀ X0 X1 : G, (M.op y (M.op (M.op x y) (M.op X0 X1))) = (M.op (M.op X0 X1) (M.op X1 (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq688 X0 X1
       have i₂ := eq53 X0 X1
       grind)
    | exact superpose eq53 eq688
    | exact resolve eq688 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq114 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq798 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq797
    | exact resolve eq797 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq801 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq798
       have r₂ := eq27
       grind)
    | exact resolve eq798 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq803 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq801
    | exact resolve eq801 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq801
  have eq805 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq803
    | exact resolve eq803 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq803
  have eq810 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq805 eq76
    | (have r₁ := eq76
       have r₂ := eq805
       grind)
    | exact resolve eq76 eq805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq816 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq805
  have eq817 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq810
  have eq872 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq93 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq902 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq817
       have r₂ := eq816
       grind)
    | exact resolve eq817 eq816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq816 eq817
  have eq906 : (τ (σ x)) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq902 eq82
    | exact resolve eq82 eq902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq902
  have eq914 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq906
    | exact resolve eq906 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq918 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq914
       have r₂ := eq75
       grind)
    | exact resolve eq914 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq920 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op (M.op X2 X1) (M.op X0 X0)) X1) = (M.op (M.op X0 X0) (M.op (M.op X2 X1) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X0 X1 X2
       have i₂ := eq53 (M.op X2 X1) (M.op X0 X0)
       grind)
    | exact superpose eq53 eq65
    | (have j0 := eq65 X0 X1 X2
       grind)
    | (have r₁ := eq65 (M.op (M.op X0 X1) (M.op X0 X1)) (M.op X1 (M.op X0 X1)) X2
       have r₂ := eq53 X0 X1
       grind)
    | (have r₁ := eq65 (M.op X1 (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1)) X2
       have r₂ := eq53 X0 X1
       grind)
    | exact resolve eq65 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq922 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq918
       grind)
    | exact superpose eq918 eq72
    | exact resolve eq72 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq923 : x = (M.op x y) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq918
       grind)
    | exact superpose eq918 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq924 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq923
  have eq926 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq924
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq924
    | exact resolve eq924 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq924
  have eq927 : x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq926
  have eq928 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq922
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq922
    | exact resolve eq922 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922
  have eq931 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq927
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq927
    | exact resolve eq927 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq927
  have eq936 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq931 eq64
    | (have r₁ := eq64
       have r₂ := eq931
       grind)
    | exact resolve eq64 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq943 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x y) := by grind
  clear eq936
  have eq945 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X1 X1)) X1) = (M.op (M.op X1 X1) (M.op (M.op X0 X1) (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq920 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920
  have eq950 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq928 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq951 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq950
  have eq955 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq951
    | exact resolve eq951 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq951
  have eq956 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq955
  have eq961 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq956
    | exact resolve eq956 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq956
  have eq963 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq961 eq27
    | exact resolve eq27 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961
  have eq1161 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq943 eq114
    | exact resolve eq114 eq943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq943
  have eq1164 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1161
  have eq1182 : ∀ X0 X1 : G, (σ y) = (M.op X0 (M.op (M.op X1 X0) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq1164 eq14
    | exact resolve eq14 eq1164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1164
  have eq1726 : (σ y) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1182 (M.op sF1 sF1) x
       have i₂ := eq682 sF1 x
       grind)
    | exact superpose eq682 eq1182
    | exact resolve eq1182 eq682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682 eq1182
  have eq1759 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1726
       have i₂ := eq53 sF1 sF1
       grind)
    | exact superpose eq53 eq1726
    | exact resolve eq1726 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1726
  have eq1772 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (σ y))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1759 eq622
    | exact resolve eq622 eq1759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1759
  have eq2731 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op x y)) (σ (M.op x y))))) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq1772 eq622
    | exact resolve eq622 eq1772
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622 eq1772
  have eq2747 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq51 eq2731
    | exact resolve eq2731 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq2731
  have eq2751 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq931 eq2747
    | exact resolve eq2747 eq931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq931 eq2747
  have eq2766 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq2751
  have eq2769 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq2766
    | exact resolve eq2766 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2766
  have eq2770 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2769
       have r₂ := eq27
       grind)
    | exact resolve eq2769 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2769
  have eq2863 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2770 eq20
    | exact resolve eq20 eq2770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2865 : ∀ X0 : G, (M.op y (M.op y (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2770 eq50
    | exact resolve eq50 eq2770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2868 : y ≠ y ∨ x = y ∨ x = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2770 eq75
    | (have r₁ := eq75
       have r₂ := eq2770
       grind)
    | exact resolve eq75 eq2770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq2869 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2770 eq125
    | exact resolve eq125 eq2770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq2879 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ (M.op x y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2770 eq316
    | exact resolve eq316 eq2770
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq2887 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq2770
  have eq2888 : x = y ∨ x = (k y x) ∨ x = (M.op x y) := by grind
  clear eq2868
  have eq2892 : ∀ X0 : G, (τ (k (σ y) X0)) = (τ (k (σ (M.op x y)) X0)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2879 X0
       have i₂ := eq270 X0
       grind)
    | exact superpose eq270 eq2879
    | exact resolve eq2879 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270 eq2879
  have eq2898 : ∀ X0 : G, (k (σ y) X0) = (k (σ (M.op x y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq2869 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq2869
    | exact resolve eq2869 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq2869
  have eq2902 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2863
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2863
    | exact resolve eq2863 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2863
  have eq2931 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2902 eq963
    | (have r₁ := eq963
       have r₂ := eq2902
       grind)
    | exact resolve eq963 eq2902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq963 eq2902
  have eq3015 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2931
  have eq3016 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq3015
  have eq3135 : (σ x) ≠ (σ x) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq3016 eq64
    | (have r₁ := eq64
       have r₂ := eq3016
       grind)
    | exact resolve eq64 eq3016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq3016
  have eq3162 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq3135
  have eq3445 : ∀ X0 : G, (k (τ (σ y)) X0) = (τ (k (σ (M.op x y)) (σ X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2898 eq293
    | exact resolve eq293 eq2898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2898
  have eq3490 : ∀ X0 : G, (k (τ (σ (M.op x y))) X0) = (k (τ (σ y)) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq3445 x
       have i₂ := eq293 sF1 x
       grind)
    | exact superpose eq293 eq3445
    | exact resolve eq3445 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293 eq3445
  have eq3495 : ∀ X0 : G, (k y X0) = (k (τ (σ (M.op x y))) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq3490
    | exact resolve eq3490 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq3490
  have eq3498 : ∀ X0 : G, (k y X0) = (k (M.op x y) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30 eq3495
    | exact resolve eq3495 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq3495
  have eq5525 : x = (k y x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq2888
       have r₂ := eq2887
       grind)
    | exact resolve eq2888 eq2887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2888
  have eq5692 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq72
       have i₂ := eq5525
       grind)
    | exact superpose eq5525 eq72
    | exact resolve eq72 eq5525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5525
  have eq5700 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5692
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq5692
    | exact resolve eq5692 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5692
  have eq5718 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5700 eq3162
    | exact resolve eq3162 eq5700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3162 eq5700
  have eq5723 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq5718
  have eq5849 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq945 X0 X0
       have i₂ := eq53 X0 X0
       grind)
    | exact superpose eq53 eq945
    | exact resolve eq945 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5856 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) (k (M.op (M.op X0 X0) (M.op X0 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq677 (M.op X0 X0) X1 X2
       have i₂ := eq945 X0 X0
       grind)
    | exact superpose eq945 eq677
    | exact resolve eq677 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677 eq945
  have eq5902 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) (k (M.op X0 (M.op X0 X0)) X0)) (k (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5856 X1 X1 X2
       have i₂ := eq53 X1 X1
       grind)
    | exact superpose eq53 eq5856
    | exact resolve eq5856 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq5856
  have eq5908 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = (k (M.op X0 (M.op X0 X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq5849 X0
       have i₂ := eq691 X0 X0
       grind)
    | exact superpose eq691 eq5849
    | exact resolve eq5849 eq691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691 eq5849
  have eq5946 : ∀ X0 : G, (k (M.op X0 (M.op X0 X0)) X0) = X0 := by
    intro X0
    first
    | exact superpose eq50 eq5908
    | exact resolve eq5908 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5908
  have eq6161 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq95 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq95
    | (have j0 := eq95 y
       grind)
    | exact resolve eq95 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq6188 : (M.op (σ y) (σ y)) = (σ (k y y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6161
  have eq6194 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6188
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq6188
    | exact resolve eq6188 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq6188
  have eq6205 : (M.op (σ y) (σ y)) = (k (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6194
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq6194 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6194
  have eq11176 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq872 x y
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq872
    | (have j0 := eq872 x y
       grind)
    | exact resolve eq872 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq11213 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11176
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11176
    | exact resolve eq11176 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11176
  have eq11265 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11213
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11213
    | exact resolve eq11213 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11213
  have eq11314 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11265
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11265
    | exact resolve eq11265 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11265
  have eq11358 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11314
    | exact resolve eq11314 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11314
  have eq11393 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq11358
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11358
    | exact resolve eq11358 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11358
  have eq11421 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq11393
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11393
    | exact resolve eq11393 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11393
  have eq11435 : (σ x) ≠ (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11421
    | exact resolve eq11421 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11421
  have eq18939 : (τ (M.op (σ y) (σ y))) = (τ (k (σ (M.op x y)) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6205 eq2892
    | exact resolve eq2892 eq6205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2892
  have eq18959 : (τ (M.op (σ y) (σ y))) = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq150 eq18939
    | exact resolve eq18939 eq150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq18939
  have eq19294 : (τ (σ x)) = (k (M.op x y) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5723 eq18959
    | exact resolve eq18959 eq5723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5723 eq18959
  have eq19343 : (τ (σ x)) = (k (M.op x y) y) ∨ x = (M.op x y) := by grind
  clear eq19294
  have eq19346 : x = (k (M.op x y) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq19343
    | exact resolve eq19343 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq19343
  have eq19357 : x = (k y y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq19346 eq3498
    | exact resolve eq3498 eq19346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3498 eq19346
  have eq19366 : x = (k y y) ∨ x = (M.op x y) := by grind
  clear eq19357
  have eq19413 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq19366
       grind)
    | exact superpose eq19366 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq19366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19426 : y = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq19413
  have eq42077 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6205 eq109
    | exact resolve eq109 eq6205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq6205
  have eq521386 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X2) X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5902 X0 X1 X2
       have i₂ := eq5946 X0
       grind)
    | exact superpose eq5946 eq5902
    | exact resolve eq5902 eq5946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5902 eq5946
  have eq522097 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq521386 X1 y (M.op y (M.op X0 X0))
       have i₂ := eq2865 X0
       grind)
    | exact superpose eq2865 eq521386
    | exact resolve eq521386 eq2865
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2865
  have eq1859993 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq19426
       grind)
    | exact superpose eq19426 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq19426
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19426
       grind)
    | exact resolve eq13 eq19426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19426
  have eq1860399 : y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq1859993
  have eq1881930 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19366
       have i₂ := eq1860399
       grind)
    | exact superpose eq1860399 eq19366
    | exact resolve eq19366 eq1860399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19366 eq1860399
  have eq1882174 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq1881930
  have eq1882329 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq1882174
       have r₂ := eq2887
       grind)
    | exact resolve eq1882174 eq2887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2887 eq1882174
  have eq1883143 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq522097 y y
       have i₂ := eq1882329
       grind)
    | exact superpose eq1882329 eq522097
    | exact resolve eq522097 eq1882329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq522097 eq1882329
  have eq1883246 : x = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq1883143
  have eq1883294 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1883246
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1883246
    | exact resolve eq1883246 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883246
  have eq1883295 : x = (M.op x y) := by grind
  clear eq1883294
  have eq1883557 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1883295 eq20
    | exact resolve eq20 eq1883295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1883559 : ∀ X0 : G, (M.op y (M.op x (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq1883295 eq50
    | exact resolve eq50 eq1883295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1883561 : x ≠ x ∨ (M.op y y) = (k y x) := by
    first
    | exact superpose eq1883295 eq63
    | (have r₁ := eq63
       have r₂ := eq1883295
       grind)
    | exact resolve eq63 eq1883295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq1884025 : (M.op y y) = (k y x) := by grind
  clear eq1883561
  have eq1884189 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1883557
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1883557
    | exact resolve eq1883557 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883557
  have eq1884210 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1884189 eq26
    | exact resolve eq26 eq1884189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1884359 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1884189 eq11435
    | exact resolve eq11435 eq1884189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11435
  have eq1885401 : (σ (M.op x y)) ≠ (k (σ y) (σ (M.op x y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1884359
       have r₂ := eq27
       grind)
    | exact resolve eq1884359 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1884359
  have eq1886859 : (k (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq1884025
       grind)
    | exact superpose eq1884025 eq72
    | exact resolve eq72 eq1884025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1884025
  have eq1887054 : (k (σ y) (σ (M.op x y))) = (σ (M.op y y)) := by
    first
    | exact superpose eq1884189 eq1886859
    | exact resolve eq1886859 eq1884189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1886859
  have eq1888701 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq521386 X1 y (M.op x (M.op X0 X0))
       have i₂ := eq1883559 X0
       grind)
    | exact superpose eq1883559 eq521386
    | exact resolve eq521386 eq1883559
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521386 eq1883559
  have eq1894286 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq1888701 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1888701
    | (have j0 := eq1888701 x y
       grind)
    | exact resolve eq1888701 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1896322 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq1883295 eq1894286
    | exact resolve eq1894286 eq1883295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894286
  have eq1896924 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq1896322
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1896322
    | exact resolve eq1896322 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1896322
  have eq1897214 : x = (M.op y y) := by
    first
    | exact superpose eq1883295 eq1896924
    | exact resolve eq1896924 eq1883295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1883295 eq1896924
  have eq1897472 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq42077
       have i₂ := eq1897214
       grind)
    | exact superpose eq1897214 eq42077
    | exact resolve eq42077 eq1897214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42077
  have eq1897478 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1887054
       have i₂ := eq1897214
       grind)
    | exact superpose eq1897214 eq1887054
    | exact resolve eq1887054 eq1897214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1887054 eq1897214
  have eq1898694 : (σ x) = (k (σ y) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1897478
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1897478
    | exact resolve eq1897478 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897478
  have eq1898697 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1897472
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1897472
    | exact resolve eq1897472 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897472
  have eq1898936 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) := by
    first
    | exact superpose eq1884189 eq1898694
    | exact resolve eq1898694 eq1884189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1898694
  have eq1898938 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1884189 eq1898697
    | exact resolve eq1898697 eq1884189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1898697
  have eq1899073 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq1898936
       have r₂ := eq1885401
       grind)
    | exact resolve eq1898936 eq1885401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1885401 eq1898936
  have eq1899205 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq1899073 eq27
    | exact resolve eq27 eq1899073
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1899073
  have eq1905865 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1898938 eq1888701
    | exact resolve eq1888701 eq1898938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1888701 eq1898938
  have eq1905873 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1884210 eq1905865
    | exact resolve eq1905865 eq1884210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1884210 eq1905865
  have eq1906368 : x = y := by
    first
    | (have r₁ := eq1905873
       have r₂ := eq27
       grind)
    | exact resolve eq1905873 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1905873
  have eq1906798 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1906368
       grind)
    | exact superpose eq1906368 eq24
    | exact resolve eq24 eq1906368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1906368
  have eq1907958 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1906798
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1906798
    | exact resolve eq1906798 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1906798
  have eq1908201 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq1884189 eq1907958
    | exact resolve eq1907958 eq1884189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1884189 eq1907958
  have eq1908317 : False := by grind
  exact eq1908317

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxy_pyx_pxy_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq31 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op (M.op (M.op X0 X2) (M.op X1 X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq31 X1 (M.op (M.op X2 X1) (M.op X0 X0))
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq31
    | exact resolve eq31 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9 X0 X0 X0
       have i₂ := eq31 X0 X0
       grind)
    | exact superpose eq31 eq9
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X3 (M.op (M.op X2 X3) (M.op X1 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X0 X1) X3 X2
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq9
    | exact resolve eq9 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X1 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 (M.op X0 X0)) X0
       have i₂ := eq59 X0
       grind)
    | exact superpose eq59 eq9
    | exact resolve eq9 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq80 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq14 (M.op (M.op X1 X1) X0) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq80 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq80
    | (have j0 := eq80 (σ X0) (σ X1)
       grind)
    | exact resolve eq80 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X1
       have i₂ := eq80 X0 X1
       grind)
    | (have i₁ := eq31 X0 X1
       have i₂ := eq80 (M.op X0 X1) X1
       grind)
    | exact superpose eq80 eq31
    | (have j1 := eq80 (M.op X1 X0) X0
       grind)
    | exact resolve eq31 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq96 : ∀ X1 X3 : G, (M.op X3 X3) = (M.op (M.op X1 (M.op X3 X3)) X3) := by
    intro X1 X3
    first
    | (have i₁ := eq57 x X3 (M.op (M.op x x) (M.op X1 X1))
       have i₂ := eq9 X1 x x
       grind)
    | exact superpose eq9 eq57
    | exact resolve eq57 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq139 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X1 (M.op X2 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X0 X0))
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq9
    | exact resolve eq9 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq96 X1 (M.op X1 (M.op X1 X1))
       have i₂ := eq66 X1 X1
       grind)
    | exact superpose eq66 eq96
    | exact resolve eq96 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq96
  have eq206 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq85 X0 X1
       grind)
    | (have i₁ := eq12 X0 X0
       have i₂ := eq85 X0 X1
       grind)
    | exact superpose eq85 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq85 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq85 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq212 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq206 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq206
  have eq216 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq212 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq218 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq216 X1
       have i₂ := eq80 X0 X1
       grind)
    | (have i₁ := eq216 X0
       have i₂ := eq80 (M.op X0 X0) X1
       grind)
    | exact superpose eq80 eq216
    | (have j1 := eq80 X1 X0
       grind)
    | exact resolve eq216 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq216
  have eq458 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq218 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq459 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq458 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458
  have eq466 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq459 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq459
    | exact resolve eq459 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq470 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq466 X0
       have i₂ := eq459 X0
       grind)
    | exact superpose eq459 eq466
    | exact resolve eq466 eq459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459 eq466
  have eq749 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq83 X0 X1
       have i₂ := eq470 X1
       grind)
    | exact superpose eq470 eq83
    | (have j0 := eq83 X0 X1
       grind)
    | exact resolve eq83 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq906 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq749 x y
       grind)
    | exact superpose eq749 eq16
    | (have j1 := eq749 x y
       grind)
    | exact resolve eq16 eq749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq749
  have eq2067 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X0)) = (M.op X1 (M.op (M.op X2 X1) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 (M.op X0 X0) X2 X1
       have i₂ := eq140 X0 X0
       grind)
    | exact superpose eq140 eq62
    | exact resolve eq62 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq2070 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq62 X0 X0 x (M.op X0 X0)
       have i₂ := eq139 x X0 X0
       grind)
    | exact superpose eq139 eq62
    | exact resolve eq62 eq139
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq2121 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2070 (σ X0)
       have i₂ := eq470 X0
       grind)
    | exact superpose eq470 eq2070
    | exact resolve eq2070 eq470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq470 eq2070
  have eq2491 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X1) = (M.op X2 (M.op (M.op X3 X2) (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 (M.op X0 X1) X1 X3 X2
       have i₂ := eq2067 X1 X1 X0
       grind)
    | exact superpose eq2067 eq62
    | exact resolve eq62 eq2067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2067
  have eq2514 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2491 X0 X1 x x
       have i₂ := eq62 X1 X1 x x
       grind)
    | exact superpose eq62 eq2491
    | exact resolve eq2491 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq2491
  have eq3873 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq906
       have i₂ := eq80 x y
       grind)
    | exact superpose eq80 eq906
    | (have j1 := eq80 x y
       grind)
    | exact resolve eq906 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq906
  have eq3887 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq3873
  have eq3894 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq3887
       grind)
    | exact superpose eq3887 eq10
    | exact resolve eq10 eq3887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3887
  have eq3924 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq3894
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq3894
    | exact resolve eq3894 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3894
  have eq3925 : x = (M.op y y) := by grind
  clear eq3924
  have eq3956 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2121 y
       have i₂ := eq3925
       grind)
    | exact superpose eq3925 eq2121
    | exact resolve eq2121 eq3925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2121
  have eq3978 : x = (M.op x y) := by
    first
    | (have i₁ := eq2514 y y
       have i₂ := eq3925
       grind)
    | exact superpose eq3925 eq2514
    | exact resolve eq2514 eq3925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2514 eq3925
  have eq4977 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3956
       grind)
    | exact superpose eq3956 eq16
    | exact resolve eq16 eq3956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3956
  have eq5016 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq4977
       have i₂ := eq3978
       grind)
    | exact superpose eq3978 eq4977
    | exact resolve eq4977 eq3978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3978 eq4977
  have eq5017 : False := by grind
  exact eq5017

/-- `Equation960`: `x = y ◇ ((z ◇ y) ◇ (x ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pyy_x_pxy_pyy_pyx_Equation960 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law960 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law960.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op b b ≠ a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X2 X1) (M.op X0 X0))) = X0 := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10
    | (have j0 := eq10 X0 x
       grind)
    | exact resolve eq10 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (σ (k X0 y)) = (k (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq10
    | (have j0 := eq10 X0 y
       grind)
    | exact resolve eq10 eq25
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
  have eq51 : ∀ X0 : G, (M.op y (M.op (M.op x y) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 X0 y x
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X1 X2) (M.op X0 X0)) (M.op X0 (M.op X3 X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) (M.op X0 X0)) X2
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op (M.op X0 X1) (M.op X0 X1)) X1 X0
       have i₂ := eq14 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, X0 ≠ X1 ∨ (k (M.op (M.op X2 X1) (M.op X0 X0)) X1) = (M.op (M.op (M.op X2 X1) (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 (M.op (M.op X2 X1) (M.op X0 X0)) X1
       grind)
    | (have r₁ := eq13 (M.op (M.op X2 X0) (M.op X0 X0)) X0
       have r₂ := eq14 X0 X0 X2
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq85 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
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
  have eq97 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq100 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq74
       have i₂ := eq11 y y
       grind)
    | exact superpose eq11 eq74
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq100
  have eq108 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq97
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98
    | exact resolve eq98 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq109
    | exact resolve eq109 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq110
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq110
    | exact resolve eq110 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq168 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq11 (σ X0) sF2
       grind)
    | exact superpose eq11 eq40
    | (have j1 := eq11 (σ X0) (σ x)
       grind)
    | exact resolve eq40 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq190 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ X0) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq41 X0
       have i₂ := eq11 (σ X0) sF3
       grind)
    | exact superpose eq11 eq41
    | (have j1 := eq11 (σ X0) (σ y)
       grind)
    | exact resolve eq41 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq471 : ∀ X0 : G, (M.op X0 (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq14 X0 X0 X0
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq474 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq52 (M.op X1 X0)
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op X2 (M.op (M.op X3 X2) (M.op X0 (M.op X1 X0)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) X2 X3
       have i₂ := eq54 X1 X0
       grind)
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527 : ∀ X0 X3 X4 : G, (M.op (M.op X0 (M.op X3 X3)) (M.op X3 (M.op X4 X4))) = X4 := by
    intro X0 X3 X4
    first
    | (have i₁ := eq53 X3 x (M.op (M.op x x) (M.op X0 X0)) X4
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 (M.op X1 X1) X1 X2 X1
       have i₂ := eq54 X1 X1
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq558 : ∀ X0 X3 : G, (M.op X0 X0) = (M.op (M.op X3 (M.op X0 X0)) X0) := by
    intro X0 X3
    first
    | (have i₁ := eq54 (M.op (M.op x x) (M.op X0 X0)) (M.op X0 (M.op X3 X3))
       have i₂ := eq53 X0 x x X3
       grind)
    | exact superpose eq53 eq54
    | exact resolve eq54 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq612 : ∀ X0 X1 : G, (k (M.op (M.op X0 X1) (M.op X1 X1)) X1) = (M.op (M.op (M.op X0 X1) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have j0 := eq66 X1 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq743 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq91 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq1381 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op y (M.op (M.op x y) X0)) := by
    intro X0
    first
    | (have i₁ := eq51 (M.op X0 (M.op X0 X0))
       have i₂ := eq527 X0 X0 X0
       grind)
    | exact superpose eq527 eq51
    | exact resolve eq51 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1382 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op X0 (M.op X0 X0))
       have i₂ := eq527 X0 X0 X0
       grind)
    | exact superpose eq527 eq52
    | exact resolve eq52 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1392 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq558 (M.op x (M.op x x)) x
       have i₂ := eq527 x x x
       grind)
    | exact superpose eq527 eq558
    | exact resolve eq558 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1627 : ∀ X0 : G, (M.op X0 (M.op y (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq471 X0
       have i₂ := eq1381 X0
       grind)
    | exact superpose eq1381 eq471
    | exact resolve eq471 eq1381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1654 : (M.op (M.op x y) y) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op y (M.op y y)))) := by
    first
    | exact superpose eq1381 eq474
    | exact resolve eq474 eq1381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381
  have eq1665 : (M.op y y) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq474 eq1654
    | exact resolve eq1654 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1654
  have eq1698 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | exact superpose eq51 eq1627
    | exact resolve eq1627 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq1627
  have eq1893 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ y) (σ y))))) := by
    first
    | exact superpose eq1382 eq474
    | exact resolve eq474 eq1382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382
  have eq1904 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq474 eq1893
    | exact resolve eq1893 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq1893
  have eq5485 : ∀ X0 X1 : G, (M.op X1 X1) = (k (M.op (M.op X0 X1) (M.op X1 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq612 X0 X1
       have i₂ := eq558 X1 (M.op X0 X1)
       grind)
    | exact superpose eq558 eq612
    | exact resolve eq612 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq5514 : ∀ X0 : G, (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op (M.op X0 (M.op X0 X0)) (M.op X0 (M.op X0 X0)))) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5485 (M.op (M.op x x) (M.op X0 (M.op X0 X0))) (M.op X0 (M.op X0 X0))
       have i₂ := eq553 X0 x x
       grind)
    | exact superpose eq553 eq5485
    | exact resolve eq5485 eq553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553 eq5485
  have eq5619 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (k (M.op X0 (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0)))) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5514 X0
       have i₂ := eq54 X0 (M.op X0 X0)
       grind)
    | exact superpose eq54 eq5514
    | exact resolve eq5514 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq5514
  have eq5672 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 (M.op X0 X0))) = (k (M.op X0 X0) (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq5619 X0
       have i₂ := eq477 X0 X0 X0 X0
       grind)
    | exact superpose eq477 eq5619
    | exact resolve eq5619 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477 eq5619
  have eq5711 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq5672 X0
       have i₂ := eq1392 X0 X0
       grind)
    | exact superpose eq1392 eq5672
    | exact resolve eq5672 eq1392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392 eq5672
  have eq5801 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op (M.op X0 (M.op X0 X0)) X0)) := by
    intro X0
    first
    | (have i₁ := eq5711 (M.op x (M.op x x))
       have i₂ := eq527 x x x
       grind)
    | exact superpose eq527 eq5711
    | exact resolve eq5711 eq527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5711
  have eq5825 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5801 X0
       have i₂ := eq558 X0 X0
       grind)
    | exact superpose eq558 eq5801
    | exact resolve eq5801 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5801
  have eq5927 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq168 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq168
    | (have j0 := eq168 x
       grind)
    | exact resolve eq168 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq5952 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq5927
  have eq5959 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq5952
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq5952
    | exact resolve eq5952 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq5952
  have eq5967 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq5959
       have r₂ := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq5959 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5959
  have eq5973 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq5967 eq50
    | exact resolve eq50 eq5967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq6108 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq190 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq190
    | (have j0 := eq190 y
       grind)
    | exact resolve eq190 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq190
  have eq6132 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq6108
  have eq6138 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq6132
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq6132
    | exact resolve eq6132 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq6132
  have eq6148 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq6138
       have r₂ := eq13 (σ y) (σ y)
       grind)
    | exact resolve eq6138 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6138
  have eq6156 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq6148 eq85
    | exact resolve eq85 eq6148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq17090 : (σ (M.op y y)) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq6148 eq107
    | exact resolve eq107 eq6148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq6148
  have eq17156 : (σ (M.op x x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq5967 eq108
    | exact resolve eq108 eq5967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq5967
  have eq17261 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq111 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq17262 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq17261
    | exact resolve eq17261 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17261
  have eq17270 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq17262
       have r₂ := eq28
       grind)
    | exact resolve eq17262 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17262
  have eq17272 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq17270
    | exact resolve eq17270 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17270
  have eq17274 : (τ (σ y)) = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq17272 eq5973
    | exact resolve eq5973 eq17272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5973 eq17272
  have eq17376 : y = (k x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq17274
    | exact resolve eq17274 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq17274
  have eq18796 : y = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq11 x x
       have i₂ := eq17376
       grind)
    | exact superpose eq17376 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq17376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18797 : y = (M.op x x) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18796
  have eq19649 : (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5825 x
       have i₂ := eq18797
       grind)
    | exact superpose eq18797 eq5825
    | exact resolve eq5825 eq18797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19686 : x ≠ y ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq19702 : (M.op x y) = (k x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19649
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq19649
    | exact resolve eq19649 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19649
  have eq20426 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq19702
       grind)
    | exact superpose eq19702 eq45
    | exact resolve eq45 eq19702
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq19702
  have eq20448 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq20426
    | exact resolve eq20426 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20426
  have eq31190 : (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17156
       have i₂ := eq18797
       grind)
    | exact superpose eq18797 eq17156
    | exact resolve eq17156 eq18797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17156 eq18797
  have eq31259 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq31190
       have r₂ := eq19686
       grind)
    | exact resolve eq31190 eq19686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19686 eq31190
  have eq31268 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq31259
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31259
    | exact resolve eq31259 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31259
  have eq31318 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31268 eq5825
    | exact resolve eq5825 eq31268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31268
  have eq31374 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq31318
    | exact resolve eq31318 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31318
  have eq102297 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31374 eq20448
    | exact resolve eq20448 eq31374
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20448 eq31374
  have eq102304 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq102297
  have eq102310 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq102304
       have r₂ := eq28
       grind)
    | exact resolve eq102304 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102304
  have eq102344 : x = (M.op x (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq471 x
       have i₂ := eq102310
       grind)
    | exact superpose eq102310 eq471
    | exact resolve eq471 eq102310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq471
  have eq102397 : (k x x) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5825 x
       have i₂ := eq102310
       grind)
    | exact superpose eq102310 eq5825
    | exact resolve eq5825 eq102310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5825 eq102310
  have eq104725 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq17376
       have i₂ := eq102397
       grind)
    | exact superpose eq102397 eq17376
    | exact resolve eq17376 eq102397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17376 eq102397
  have eq104751 : y = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq104725
  have eq104797 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq102344
       have i₂ := eq104751
       grind)
    | exact superpose eq104751 eq102344
    | exact resolve eq102344 eq104751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102344 eq104751
  have eq104956 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq104797
  have eq105048 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq104956
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq104956
    | exact resolve eq104956 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104956
  have eq105049 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq105048
  have eq105091 : ∀ X0 : G, (M.op (σ y) (M.op (σ x) (M.op X0 X0))) = X0 ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq105049 eq52
    | exact resolve eq52 eq105049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq105131 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105049 eq1904
    | exact resolve eq1904 eq105049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1904
  have eq105493 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq105131
    | exact resolve eq105131 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105131
  have eq109629 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105493 eq105091
    | exact resolve eq105091 eq105493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105091 eq105493
  have eq109722 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by grind
  clear eq109629
  have eq109829 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq105049 eq109722
    | exact resolve eq109722 eq105049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105049 eq109722
  have eq109934 : (σ y) = (M.op (σ y) (M.op (σ x) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq109829
  have eq110267 : ∀ X0 : G, (σ x) = (M.op (M.op X0 (M.op (σ y) (σ y))) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq109934 eq527
    | exact resolve eq527 eq109934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527 eq109934
  have eq110390 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq110267 x
       have i₂ := eq558 sF3 x
       grind)
    | exact superpose eq558 eq110267
    | exact resolve eq110267 eq558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq558 eq110267
  have eq110416 : (τ (σ x)) = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq110390 eq6156
    | exact resolve eq6156 eq110390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110390
  have eq110686 : x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq110416
    | exact resolve eq110416 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq110416
  have eq111302 : x = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq11 y y
       have i₂ := eq110686
       grind)
    | exact superpose eq110686 eq11
    | (have j0 := eq11 y y
       grind)
    | exact resolve eq11 eq110686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111303 : y = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq111302
  have eq266628 : y ≠ y ∨ y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq111303
       grind)
    | exact superpose eq111303 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq111303
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq111303
       grind)
    | exact resolve eq13 eq111303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266718 : x ≠ y ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq111303
  have eq266719 : y = (k y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq266628
  have eq271635 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq110686
       have i₂ := eq266719
       grind)
    | exact superpose eq266719 eq110686
    | exact resolve eq110686 eq266719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110686 eq266719
  have eq271668 : x = y ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq271635
  have eq271698 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq271668
       have r₂ := eq266718
       grind)
    | exact resolve eq271668 eq266718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266718 eq271668
  have eq271809 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1698 y
       have i₂ := eq271698
       grind)
    | exact superpose eq271698 eq1698
    | exact resolve eq1698 eq271698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271698
  have eq272004 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq271809
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq271809
    | exact resolve eq271809 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271809
  have eq272005 : x = (M.op x y) := by grind
  clear eq272004
  have eq272032 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq272005 eq21
    | exact resolve eq21 eq272005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq272126 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq272005 eq1665
    | exact resolve eq1665 eq272005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1665
  have eq272355 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq272126
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq272126
    | exact resolve eq272126 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq272126
  have eq272410 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq272032
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq272032
    | exact resolve eq272032 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272032
  have eq272415 : x = (M.op y y) := by
    first
    | exact superpose eq272005 eq272355
    | exact resolve eq272355 eq272005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272355
  have eq274069 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq272410 eq27
    | exact resolve eq27 eq272410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq274691 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq17090
       have i₂ := eq272415
       grind)
    | exact superpose eq272415 eq17090
    | exact resolve eq17090 eq272415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17090
  have eq274804 : x ≠ y ∨ x = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq272415
       grind)
    | exact superpose eq272415 eq13
    | exact resolve eq13 eq272415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272415
  have eq275003 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq274691
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq274691
    | exact resolve eq274691 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274691
  have eq275029 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq272410 eq275003
    | exact resolve eq275003 eq272410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275003
  have eq284148 : (τ (σ (M.op x y))) = (k y y) ∨ x = y := by
    first
    | exact superpose eq275029 eq6156
    | exact resolve eq6156 eq275029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6156
  have eq284287 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq275029 eq1698
    | exact resolve eq1698 eq275029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1698 eq275029
  have eq284501 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq274069 eq284287
    | exact resolve eq284287 eq274069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284287
  have eq284532 : (M.op x y) = (k y y) ∨ x = y := by
    first
    | exact superpose eq31 eq284148
    | exact resolve eq284148 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq284148
  have eq284553 : x = y := by
    first
    | (have r₁ := eq284501
       have r₂ := eq28
       grind)
    | exact resolve eq284501 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284501
  have eq284571 : x = (k y y) ∨ x = y := by
    first
    | exact superpose eq272005 eq284532
    | exact resolve eq284532 eq272005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272005 eq284532
  have eq284590 : x = (k y y) := by
    first
    | (have r₁ := eq284571
       have r₂ := eq274804
       grind)
    | exact resolve eq284571 eq274804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274804 eq284571
  have eq284600 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq284553
       grind)
    | exact superpose eq284553 eq25
    | exact resolve eq25 eq284553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq285297 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq284600
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq284600
    | exact resolve eq284600 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284600
  have eq285448 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq272410 eq285297
    | exact resolve eq285297 eq272410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285297
  have eq286218 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq285448 eq274069
    | exact resolve eq274069 eq285448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274069 eq285448
  have eq286440 : x = (k x x) := by
    first
    | (have i₁ := eq284590
       have i₂ := eq284553
       grind)
    | exact superpose eq284553 eq284590
    | exact resolve eq284590 eq284553
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284553 eq284590
  have eq286481 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq743 x x
       have i₂ := eq286440
       grind)
    | exact superpose eq286440 eq743
    | (have j0 := eq743 x x
       grind)
    | exact resolve eq743 eq286440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743 eq286440
  have eq286484 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq286481
  have eq286485 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq286484
  have eq286498 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq286485
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq286485
    | exact resolve eq286485 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq286485
  have eq286526 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq272410 eq286498
    | exact resolve eq286498 eq272410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq272410 eq286498
  have eq290319 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq286526 eq286218
    | exact resolve eq286218 eq286526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286218 eq286526
  have eq290320 : False := by grind
  exact eq290320
