import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation639`: `x = x ◇ (y ◇ ((y ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation639 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law639 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law639.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq53 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq53 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq53 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq54 (σ X0)
       grind)
    | exact superpose eq54 eq15
    | exact resolve eq15 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq56
  have eq79 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X0 X1
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq85
    | (have j0 := eq85 X0 X1
       grind)
    | exact resolve eq85 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq85
  have eq185 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 X0 (σ X0)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq196 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq185 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185
  have eq201 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq196 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq196 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq196 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq212 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq201 X0 X1
       have j1 := eq79 X0 (σ X1)
       grind)
    | (have r₁ := eq201 X0 X1
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq201 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq201
  have eq219 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq212 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq212
    | (have j0 := eq212 X0 X1
       grind)
    | exact resolve eq212 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq220 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq219 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq219
  have eq224 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq220 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq220
    | exact resolve eq220 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq220 x y
       grind)
    | exact superpose eq220 eq16
    | exact resolve eq16 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220
  have eq316 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq224 X0 (τ X1)
       grind)
    | exact superpose eq224 eq17
    | exact resolve eq17 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq224
  have eq338 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq316 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq316
    | exact resolve eq316 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq349 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq338 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq338
    | exact resolve eq338 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq338
  have eq373 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq235
       have i₂ := eq349 x y
       grind)
    | exact superpose eq349 eq235
    | exact resolve eq235 eq349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235 eq349
  have eq374 : False := by grind
  exact eq374

/-- `Equation639`: `x = x ◇ (y ◇ ((y ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pxy_Equation639 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law639 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law639.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 = X1 ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X1 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq19 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq20 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (k X1 X1) ≠ (k X0 X0) := by
    intro X0 X1
    grind
  clear eq18
  have eq21 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (k X1 X1) = (k X0 X0) := by
    intro X0 X1
    grind
  clear eq19
  have eq22 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq15
    | exact resolve eq15 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : (M.op (σ x) (σ y)) ≠ (σ (k y x)) ∨ x = y ∨ (k x x) ≠ (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq20 y x
       grind)
    | exact superpose eq20 eq9
    | (have j1 := eq20 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq20 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq20 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : (k x x) ≠ (k y y) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq561
       have i₂ := eq10 y x
       grind)
    | exact superpose eq10 eq561
    | exact resolve eq561 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq1212 : (M.op (σ x) (σ y)) ≠ (σ (k x y)) ∨ x = y ∨ (k x x) = (k y y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq21 x y
       grind)
    | exact superpose eq21 eq9
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq9
       have r₂ := eq21 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq9
       have r₂ := eq21 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq9 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1220 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (k x x) = (k y y) := by
    first
    | (have i₁ := eq1212
       have i₂ := eq10 x y
       grind)
    | exact superpose eq10 eq1212
    | exact resolve eq1212 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1212
  have eq1221 : (k (σ x) (σ y)) ≠ (k (σ x) (σ y)) ∨ x = y ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1220
       have i₂ := eq21 (σ x) (σ y)
       grind)
    | exact superpose eq21 eq1220
    | (have j1 := eq21 x y
       grind)
    | (have r₁ := eq1220
       have r₂ := eq21 (σ x) (σ y)
       grind)
    | (have r₁ := eq1220
       have r₂ := eq21 (M.op (σ x) (σ y)) (k (σ x) (σ y))
       grind)
    | (have r₁ := eq1220
       have r₂ := eq21 (k (σ x) (σ y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1220 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1220
  have eq1223 : x = y ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1221
  have eq1299 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1223
       grind)
    | exact superpose eq1223 eq9
    | exact resolve eq9 eq1223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq1300 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1299
  have eq1301 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1300
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1300
    | exact resolve eq1300 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1300
  have eq1302 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1301
  have eq1303 : (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by grind
  clear eq1302
  have eq1381 : (k (σ y) (σ y)) = (σ (k x x)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq10 y y
       have i₂ := eq1303
       grind)
    | exact superpose eq1303 eq10
    | exact resolve eq10 eq1303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303
  have eq1383 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1381
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1381
    | exact resolve eq1381 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1381
  have eq1384 : (k (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1383
  have eq1388 : (k y y) = (τ (k (σ x) (σ x))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22 y y
       have i₂ := eq1384
       grind)
    | exact superpose eq1384 eq22
    | exact resolve eq22 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1435 : (k x x) = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1388
       have i₂ := eq22 x x
       grind)
    | exact superpose eq22 eq1388
    | exact resolve eq1388 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1388
  have eq1457 : (k x x) ≠ (k x x) ∨ x = y ∨ (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq566
       have i₂ := eq1435
       grind)
    | exact superpose eq1435 eq566
    | (have r₁ := eq566
       have r₂ := eq1435
       grind)
    | exact resolve eq566 eq1435
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566 eq1435
  have eq1460 : (M.op (σ x) (σ y)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1457
  have eq1464 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq1460
       have i₂ := eq20 (σ y) (σ x)
       grind)
    | exact superpose eq20 eq1460
    | (have j1 := eq20 (σ x) (σ y)
       grind)
    | (have r₁ := eq1460
       have r₂ := eq20 (σ y) (σ x)
       grind)
    | (have r₁ := eq1460
       have r₂ := eq20 (M.op (σ x) (σ y)) (k (σ y) (σ x))
       grind)
    | (have r₁ := eq1460
       have r₂ := eq20 (k (σ y) (σ x)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq1460 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1460
  have eq1465 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1464
  have eq1466 : x = y ∨ (σ x) = (σ y) ∨ (k (σ y) (σ y)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1465
  have eq1468 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1466
       have r₂ := eq1384
       grind)
    | exact resolve eq1466 eq1384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1384 eq1466
  have eq1469 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1468
       grind)
    | exact superpose eq1468 eq9
    | exact resolve eq9 eq1468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468
  have eq1470 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) ∨ (σ x) = (σ y) := by grind
  clear eq1469
  have eq1471 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1470
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1470
    | exact resolve eq1470 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1470
  have eq1472 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq1471
  have eq1473 : (σ x) = (σ y) := by grind
  clear eq1472
  have eq1475 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq15 y
       have i₂ := eq1473
       grind)
    | exact superpose eq1473 eq15
    | exact resolve eq15 eq1473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1473
  have eq1522 : x = y := by
    first
    | (have i₁ := eq1475
       have i₂ := eq15 x
       grind)
    | exact superpose eq15 eq1475
    | exact resolve eq1475 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1475
  have eq1525 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq9
       have i₂ := eq1522
       grind)
    | exact superpose eq1522 eq9
    | exact resolve eq9 eq1522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1522
  have eq1526 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq1525
  have eq1527 : (k (σ x) (σ x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq1526
       have i₂ := eq10 x x
       grind)
    | exact superpose eq10 eq1526
    | exact resolve eq1526 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1526
  have eq1528 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) := by grind
  clear eq1527
  have eq1529 : False := by grind
  exact eq1529

/-- `Equation639`: `x = x ◇ (y ◇ ((y ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_pyy_pxy_Equation639 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law639 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law639.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq25 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq29 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq30 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    grind
  clear eq29
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq63 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq30 X0
       grind)
    | exact superpose eq30 eq10
    | exact resolve eq10 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq286 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq390 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq397 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X1) (τ X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq45 X1 X0
       have i₂ := eq14 (τ X0) (τ X1)
       grind)
    | exact superpose eq14 eq45
    | (have j1 := eq14 (τ X0) (τ X1)
       grind)
    | exact resolve eq45 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq406 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X1 X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq397 X0 X1
       have i₂ := eq63 X1
       grind)
    | exact superpose eq63 eq397
    | (have j0 := eq397 X0 X1
       grind)
    | exact resolve eq397 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq397
  have eq407 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq390 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq390
    | (have j0 := eq390 X0 X1
       grind)
    | exact resolve eq390 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq390
  have eq1633 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq407 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq407
    | (have j0 := eq407 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | exact resolve eq407 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1653 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ (τ X0)) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ (τ X0)) (σ X1)) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq407 (τ X0) X1
       grind)
    | exact superpose eq407 eq18
    | (have j1 := eq407 (τ X0) X1
       grind)
    | exact resolve eq18 eq407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq407
  have eq1704 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ (τ X0)) (σ X1)) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1653 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1653
    | (have j0 := eq1653 X0 X1
       grind)
    | exact resolve eq1653 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1653
  have eq1725 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (τ X0)) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1704 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1704
    | (have j0 := eq1704 X0 X1
       grind)
    | exact resolve eq1704 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1704
  have eq1742 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op X0 (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1725 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1725
    | (have j0 := eq1725 X0 X1
       grind)
    | exact resolve eq1725 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1725
  have eq2876 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (M.op X1 (σ (σ X0))) ∨ (σ (σ X0)) = X1 ∨ (σ (σ (M.op X0 X0))) = (k X1 (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq286 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq286
    | (have j0 := eq286 (σ X0) X1
       grind)
    | (have r₁ := eq286 X0 (σ X0)
       have r₂ := eq22 X0
       grind)
    | exact resolve eq286 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq286
  have eq4647 : ∀ X0 X1 : G, (τ (k X0 X1)) ≠ (τ (M.op X1 X1)) ∨ (M.op (τ X0) (τ X1)) = (τ (M.op X1 X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have j0 := eq406 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406
  have eq4675 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (M.op (σ X1) (σ X1))) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X0)) (τ (σ X1))) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4647 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4647
    | (have j0 := eq4647 (σ X0) (σ X1)
       grind)
    | exact resolve eq4647 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4647
  have eq4737 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ (M.op X1 X1))) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X0)) (τ (σ X1))) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4675 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq4675
    | (have j0 := eq4675 X0 X1
       grind)
    | exact resolve eq4675 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4675
  have eq4770 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (τ (σ (k X0 X1))) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X0)) (τ (σ X1))) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4737 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq4737
    | (have j0 := eq4737 X0 X1
       grind)
    | exact resolve eq4737 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4737
  have eq4797 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (τ (M.op (σ X1) (σ X1))) = (M.op (τ (σ X0)) (τ (σ X1))) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4770 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq4770
    | (have j0 := eq4770 X0 X1
       grind)
    | exact resolve eq4770 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4770
  have eq4821 : ∀ X0 X1 : G, (M.op (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4797 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4797
    | (have j0 := eq4797 X0 X1
       grind)
    | exact resolve eq4797 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4797
  have eq4841 : ∀ X0 X1 : G, (M.op (τ (σ X0)) X1) = (τ (σ (M.op X1 X1))) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4821 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq4821
    | (have j0 := eq4821 X0 X1
       grind)
    | exact resolve eq4821 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4821
  have eq4860 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (τ (σ X0)) X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4841 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq4841
    | (have j0 := eq4841 X0 X1
       grind)
    | exact resolve eq4841 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4841
  have eq4874 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) ∨ (τ (σ X0)) = (τ (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4860 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4860
    | (have j0 := eq4860 X0 X1
       grind)
    | exact resolve eq4860 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4860
  have eq4887 : ∀ X0 X1 : G, (τ (σ X0)) = X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4874 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4874
    | (have j0 := eq4874 X0 X1
       grind)
    | exact resolve eq4874 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4874
  have eq4896 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4887 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4887
    | (have j0 := eq4887 X0 X1
       grind)
    | exact resolve eq4887 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4887
  have eq4918 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4896 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4896
    | (have j0 := eq4896 (σ X0) (σ X1)
       grind)
    | exact resolve eq4896 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4896
  have eq4946 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4918 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq4918
    | (have j0 := eq4918 X0 X1
       grind)
    | exact resolve eq4918 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4918
  have eq4956 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4946 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq4946
    | (have j0 := eq4946 X0 X1
       grind)
    | exact resolve eq4946 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4946
  have eq33133 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ X1) = (σ (σ X0)) ∨ (σ (σ (M.op X0 X0))) = (k (σ X1) (σ (σ X0))) ∨ (M.op (σ X1) (σ (σ X0))) = (σ (M.op X1 (σ X0))) ∨ (σ X1) = (σ (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2876 X0 (σ X1)
       have i₂ := eq1633 X1 (σ X0)
       grind)
    | exact superpose eq1633 eq2876
    | (have j0 := eq2876 X0 (σ X1)
       have j1 := eq1633 X1 (σ X0)
       grind)
    | (have r₁ := eq2876 X0 X1
       have r₂ := eq1633 (σ (σ (M.op X0 X0))) (M.op X1 (σ (σ X0)))
       grind)
    | (have r₁ := eq2876 X0 X1
       have r₂ := eq1633 (M.op X1 (σ (σ X0))) (σ (σ (M.op X0 X0)))
       grind)
    | exact resolve eq2876 eq1633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2876
  have eq33259 : ∀ X0 X1 : G, (σ (M.op X1 X1)) ≠ (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1633 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1633
  have eq33261 : ∀ X0 X1 : G, (σ (M.op (σ X0) (σ X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ X1) = (σ (σ X0)) ∨ (σ (σ (M.op X0 X0))) = (k (σ X1) (σ (σ X0))) ∨ (M.op (σ X1) (σ (σ X0))) = (σ (M.op X1 (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq33133 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33133
  have eq33277 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (σ (M.op X0 X0))) ∨ (σ X1) = (σ (σ X0)) ∨ (σ (σ (M.op X0 X0))) = (k (σ X1) (σ (σ X0))) ∨ (M.op (σ X1) (σ (σ X0))) = (σ (M.op X1 (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33261 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq33261
    | (have j0 := eq33261 X0 X1
       grind)
    | exact resolve eq33261 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33261
  have eq33278 : ∀ X0 X1 : G, (σ X1) = (σ (σ X0)) ∨ (σ (σ (M.op X0 X0))) = (k (σ X1) (σ (σ X0))) ∨ (M.op (σ X1) (σ (σ X0))) = (σ (M.op X1 (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq33277 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33277
  have eq33308 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (σ (k X1 (σ X0))) ∨ (σ X1) = (σ (σ X0)) ∨ (M.op (σ X1) (σ (σ X0))) = (σ (M.op X1 (σ X0))) ∨ (M.op (σ X0) (σ X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33278 X0 X1
       have i₂ := eq15 X1 (σ X0)
       grind)
    | exact superpose eq15 eq33278
    | (have j0 := eq33278 X0 X1
       grind)
    | exact resolve eq33278 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33278
  have eq33330 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ X0)) ∨ (σ (σ (M.op X0 X0))) = (σ (k X1 (σ X0))) ∨ (σ X1) = (σ (σ X0)) ∨ (M.op (σ X1) (σ (σ X0))) = (σ (M.op X1 (σ X0))) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33308 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq33308
    | (have j0 := eq33308 X0 X1
       grind)
    | exact resolve eq33308 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33308
  have eq33343 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ X0)) ∨ (σ (σ (M.op X0 X0))) = (σ (M.op X1 (σ X0))) ∨ (σ X1) = (σ (σ X0)) ∨ (M.op (σ X1) (σ (σ X0))) = (σ (M.op X1 (σ X0))) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | exact superpose eq1742 eq33330
    | (have j0 := eq33330 X0 X1
       have j1 := eq1742 X1 X0
       grind)
    | exact resolve eq33330 eq1742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1742 eq33330
  have eq384658 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (M.op X1 (σ X0))) ∨ (M.op (σ X1) (σ (σ X0))) = (σ (M.op X1 (σ X0))) ∨ (σ X1) = (σ (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33259 X0 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq33259
    | (have j0 := eq33259 X1 (σ X0)
       grind)
    | exact resolve eq33259 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33259
  have eq384721 : ∀ X0 X1 : G, (M.op (σ X1) (σ (σ X0))) = (σ (M.op X1 (σ X0))) ∨ (σ X1) = (σ (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq384658 X0 X1
       have j1 := eq33343 X0 X1
       grind)
    | (have r₁ := eq384658 X0 X1
       have r₂ := eq33343 X0 X1
       grind)
    | (have r₁ := eq384658 X0 X1
       have r₂ := eq33343 (M.op X0 X0) (M.op X1 (σ X0))
       grind)
    | (have r₁ := eq384658 X0 X1
       have r₂ := eq33343 (σ (M.op X0 X0)) (σ (M.op X1 (σ X0)))
       grind)
    | exact resolve eq384658 eq33343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33343 eq384658
  have eq384960 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq384721 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq384721
    | (have j0 := eq384721 (M.op X1 X0) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq384721 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq384721
  have eq385178 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (M.op X0 X0))) ∨ (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq384960 X0 X1
       have i₂ := eq63 X0
       grind)
    | exact superpose eq63 eq384960
    | (have j0 := eq384960 X0 X1
       grind)
    | exact resolve eq384960 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq384960
  have eq385203 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (σ X0) = (σ X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq385178 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq385178
    | (have j0 := eq385178 X0 X1
       grind)
    | exact resolve eq385178 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385178
  have eq385539 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq385203 y x
       grind)
    | exact superpose eq385203 eq16
    | (have j1 := eq385203 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq385203 y x
       grind)
    | (have r₁ := eq16
       have r₂ := eq385203 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq385203 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq385203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385203
  have eq385562 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq385539
  have eq385621 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ (M.op x y) = (k X0 y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq385562
       grind)
    | exact superpose eq385562 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq385562
       grind)
    | exact resolve eq13 eq385562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq385730 : x = y ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have j0 := eq385621 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385621
  have eq385731 : (M.op x y) = (k x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq385730
  have eq385737 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4956 x y
       have i₂ := eq385731
       grind)
    | exact superpose eq385731 eq4956
    | (have j0 := eq4956 x y
       grind)
    | exact resolve eq4956 eq385731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4956 eq385731
  have eq385739 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq385737
  have eq385744 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq385562 eq385739
    | exact resolve eq385739 eq385562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385739
  have eq385745 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq385744
  have eq385753 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq385562 eq385745
    | exact resolve eq385745 eq385562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385562 eq385745
  have eq385757 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq385753
       have r₂ := eq16
       grind)
    | exact resolve eq385753 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385753
  have eq385760 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq385757
       grind)
    | exact superpose eq385757 eq10
    | exact resolve eq10 eq385757
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385757
  have eq385967 : x = y ∨ x = y := by
    first
    | (have i₁ := eq385760
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq385760
    | exact resolve eq385760 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385760
  have eq385968 : x = y := by grind
  clear eq385967
  have eq385971 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq385968
       grind)
    | exact superpose eq385968 eq16
    | exact resolve eq16 eq385968
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385968
  have eq385972 : False := by grind
  exact eq385972

/-- `Equation649`: `x = x ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_pxx_pxy_Equation649 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law649 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law649.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq18
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X0) X0)) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op X3 (M.op X0 (M.op X1 (M.op (M.op X2 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 (M.op (M.op X2 X0) X0)) X3 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op (M.op X1 X0) X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (M.op X1 X0) X0) X0 x
       have i₂ := eq9 X0 (M.op x (M.op (M.op X1 X0) X0)) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op (M.op X2 X0) X0)) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61 X0 X1 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq64 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k (M.op X1 (M.op (M.op X2 X0) X0)) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X1 (M.op (M.op X2 X0) X0)) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 (M.op X1 (M.op (M.op X2 X0) X0)) X0
       grind)
    | (have r₁ := eq12 (M.op X1 (M.op (M.op X2 X0) X0)) X0
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op (M.op X2 X0) X0)) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq64 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq70 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) ≠ (M.op (M.op X0 X1) X1) ∨ (k X1 (M.op (M.op X0 X1) X1)) = (M.op X1 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op (M.op X0 X1) X1)
       have i₂ := eq62 X1 X0
       grind)
    | exact superpose eq62 eq12
    | (have j0 := eq12 X1 (M.op (M.op X0 X1) X1)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op X1 X0) X0)
       have r₂ := eq62 X0 X1
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq73 : ∀ X0 X1 : G, (k X1 (M.op (M.op X0 X1) X1)) = (M.op X1 (M.op (M.op X0 X1) X1)) := by
    intro X0 X1
    first
    | (have j0 := eq70 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq291 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
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
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq292 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq291 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq291
    | (have j0 := eq291 (σ X0) (σ X1)
       grind)
    | exact resolve eq291 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq293 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq291 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq291
    | (have j0 := eq291 (τ X0) (τ X1)
       grind)
    | exact resolve eq291 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq292 X0 X1
       have i₂ := eq291 X0 X1
       grind)
    | exact superpose eq291 eq292
    | (have j0 := eq292 X0 X1
       have j1 := eq291 (σ X0) (σ X1)
       grind)
    | exact resolve eq292 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 : G, (k X0 X1) = (τ (M.op (σ X0) (σ X1))) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq292 X0 X1
       grind)
    | exact superpose eq292 eq10
    | (have j1 := eq292 X0 X1
       grind)
    | exact resolve eq10 eq292
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq564 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X1) (τ X0)
       have i₂ := eq293 X0 X1
       grind)
    | exact superpose eq293 eq12
    | (have j0 := eq12 (τ X1) (τ X0)
       have j1 := eq293 X0 X1
       grind)
    | (have r₁ := eq12 (τ X1) (τ X0)
       have r₂ := eq293 X0 X1
       grind)
    | exact resolve eq12 eq293
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq566 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq293 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq567 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (k (τ X1) (τ X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq564 X0 X1
       have j1 := eq12 (τ X1) (τ X0)
       grind)
    | (have r₁ := eq564 X0 X1
       have r₂ := eq12 (τ X1) (τ X0)
       grind)
    | exact resolve eq564 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq564
  have eq573 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X1)) ∨ (τ (k X1 X0)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq567 X0 X1
       have i₂ := eq31 X0 X1
       grind)
    | exact superpose eq31 eq567
    | (have j0 := eq567 X0 X1
       grind)
    | exact resolve eq567 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq577 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq566 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq566
    | (have j0 := eq566 (σ X0) (σ X1)
       grind)
    | exact resolve eq566 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq587 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 X1) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq577 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq577
    | (have j0 := eq577 X0 X1
       grind)
    | exact resolve eq577 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577
  have eq589 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq587 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq587
    | (have j0 := eq587 X0 X1
       grind)
    | exact resolve eq587 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq590 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op (τ (σ X0)) X1) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq589 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq589
    | (have j0 := eq589 X0 X1
       grind)
    | exact resolve eq589 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq591 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq590 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq590
    | (have j0 := eq590 X0 X1
       grind)
    | exact resolve eq590 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq594 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq591 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq591
    | (have j0 := eq591 (σ X0) (σ X1)
       grind)
    | exact resolve eq591 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591
  have eq648 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (τ (σ (k X0 X1))) ∨ (τ (k (σ X1) (σ X0))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq573 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq573
    | (have j0 := eq573 (σ X0) (σ X1)
       grind)
    | exact resolve eq573 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573
  have eq663 : ∀ X0 X1 : G, (τ (σ X0)) ≠ (k X0 X1) ∨ (τ (k (σ X1) (σ X0))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq648 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq648
    | (have j0 := eq648 X0 X1
       grind)
    | exact resolve eq648 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq666 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (τ (k (σ X1) (σ X0))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq663 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq663
    | (have j0 := eq663 X0 X1
       grind)
    | exact resolve eq663 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq668 : ∀ X0 X1 : G, (τ (k (σ X1) (σ X0))) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq666 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq666
    | (have j0 := eq666 X0 X1
       grind)
    | exact resolve eq666 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq666
  have eq669 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (k (σ X1) (σ X0))) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq668 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq668
    | (have j0 := eq668 X0 X1
       grind)
    | exact resolve eq668 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq670 : ∀ X0 X1 : G, (M.op X1 X0) = (k (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq669 X0 X1
       have i₂ := eq22 (σ X1) X0
       grind)
    | exact superpose eq22 eq669
    | (have j0 := eq669 X0 X1
       grind)
    | exact resolve eq669 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq669
  have eq671 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq670 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq670
    | (have j0 := eq670 X0 X1
       grind)
    | exact resolve eq670 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq674 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq671 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq671
    | (have j0 := eq671 (σ X0) (σ X1)
       grind)
    | exact resolve eq671 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq674 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq674
    | (have j0 := eq674 X0 X1
       grind)
    | exact resolve eq674 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq703 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op (M.op X3 X2) (M.op X4 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op X3 X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X3 X2) X4 (M.op X0 (M.op (M.op X1 X2) X2))
       have i₂ := eq63 X2 X0 X1 X3
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq712 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 X2) = (M.op (M.op X3 X2) (M.op X4 (M.op X0 (M.op (M.op X1 X2) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq703 X0 X1 X2 X3 X4
       have i₂ := eq63 X2 X0 X1 X3
       grind)
    | exact superpose eq63 eq703
    | exact resolve eq703 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq756 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq712 x x X0 X1 X0
       have i₂ := eq9 X0 x x
       grind)
    | exact superpose eq9 eq712
    | exact resolve eq712 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq712
  have eq782 : ∀ X0 X1 X2 : G, (k (M.op X1 (M.op X2 X0)) X0) = (M.op (M.op X1 (M.op X2 X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq65 X0 X1 X1
       have i₂ := eq756 X0 X1
       grind)
    | exact superpose eq756 eq65
    | exact resolve eq65 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq783 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X0 X1 X1 X3
       have i₂ := eq756 X0 X1
       grind)
    | exact superpose eq756 eq63
    | exact resolve eq63 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq784 : ∀ X0 X1 : G, (k X1 (M.op X0 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X1 X0
       have i₂ := eq756 X0 X1
       grind)
    | exact superpose eq756 eq73
    | exact resolve eq73 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq785 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq756 X0 X2
       grind)
    | exact superpose eq756 eq9
    | exact resolve eq9 eq756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756
  have eq798 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) X0) ∨ (M.op X0 X0) = (k X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op X1 (M.op X2 X0))
       have i₂ := eq785 X0 X1 X2
       grind)
    | exact superpose eq785 eq13
    | (have j0 := eq13 X0 (M.op X1 (M.op X2 X0))
       grind)
    | (have r₁ := eq13 X0 (M.op X1 (M.op X2 X0))
       have r₂ := eq785 X0 X1 X2
       grind)
    | exact resolve eq13 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq800 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 X0)) = (M.op (M.op X1 (M.op X2 X0)) X0) ∨ (M.op X0 X0) = (k X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have j0 := eq798 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq811 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (σ X0)))) = (τ (M.op (σ X0) (M.op X1 (σ X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 (M.op X1 (σ X0))
       have i₂ := eq784 X1 (σ X0)
       grind)
    | exact superpose eq784 eq28
    | exact resolve eq28 eq784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq825 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 (M.op X1 X2))) (σ X2)) = (σ (M.op (M.op X0 (M.op X1 X2)) X2)) ∨ (σ (M.op X0 (M.op X1 X2))) = (M.op (σ (M.op X0 (M.op X1 X2))) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq292 (M.op X0 (M.op X1 X2)) X2
       have i₂ := eq782 X2 X0 X1
       grind)
    | exact superpose eq782 eq292
    | (have j0 := eq292 (M.op X0 (M.op X1 X2)) X2
       grind)
    | exact resolve eq292 eq782
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1120 : ∀ X0 X2 : G, (M.op (M.op X2 X0) (M.op X2 X0)) = (k (M.op X2 X0) X0) ∨ (M.op X0 (M.op X2 X0)) = X0 := by
    intro X0 X2
    first
    | (have i₁ := eq800 (M.op X2 X0) X0 x
       have i₂ := eq785 X0 x X2
       grind)
    | exact superpose eq785 eq800
    | exact resolve eq800 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1122 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X0 (M.op X1 X2)) ∨ (M.op X2 (M.op X0 (M.op X1 X2))) = (k X2 (M.op X0 (M.op X1 X2))) ∨ (k X2 (M.op X0 (M.op X1 X2))) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 (M.op X1 X2))
       have i₂ := eq800 X2 X0 X1
       grind)
    | exact superpose eq800 eq12
    | (have j0 := eq12 X2 (M.op X0 (M.op X1 X2))
       have j1 := eq800 X2 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X1 (M.op X2 X0))
       have r₂ := eq800 X0 X1 X2
       grind)
    | exact resolve eq12 eq800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1127 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 (M.op X0 (M.op X1 X2))) X2) = (k (M.op X3 (M.op X0 (M.op X1 X2))) X2) ∨ (k X2 (M.op X0 (M.op X1 X2))) = (M.op X2 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq782 X0 X1 (M.op X1 (M.op X2 X0))
       have i₂ := eq800 X0 X1 X2
       grind)
    | exact superpose eq800 eq782
    | (have j1 := eq800 X2 X0 X1
       grind)
    | exact resolve eq782 eq800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1131 : ∀ X0 X1 X2 X3 : G, (k X2 (M.op X0 (M.op X1 X2))) = (M.op X2 X2) ∨ (M.op X2 (M.op X3 (M.op X0 (M.op X1 X2)))) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq785 X2 X3 (M.op X0 (M.op X1 X2))
       have i₂ := eq800 X2 X0 X1
       grind)
    | exact superpose eq800 eq785
    | (have j1 := eq800 X2 X0 X1
       grind)
    | exact resolve eq785 eq800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1140 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X2 X3)) = (k (M.op X2 X3) (M.op X0 (M.op X1 (M.op X2 X3)))) ∨ (M.op X3 (M.op X0 (M.op X1 (M.op X2 X3)))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq785 X3 (M.op X0 (M.op X1 (M.op X2 X3))) X2
       have i₂ := eq800 (M.op X2 X3) X0 X1
       grind)
    | exact superpose eq800 eq785
    | (have j1 := eq800 (M.op X2 X3) X0 X1
       grind)
    | exact resolve eq785 eq800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800
  have eq1150 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 (M.op X1 X2))) = (k X2 (M.op X0 (M.op X1 X2))) ∨ (k X2 (M.op X0 (M.op X1 X2))) = (M.op X2 X2) := by
    intro X0 X1 X2
    first
    | (have j0 := eq1122 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq1160 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 X2))) = (M.op X2 X2) ∨ (k X2 (M.op X0 (M.op X1 X2))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1150 X0 X1 X2
       have i₂ := eq785 X2 X0 X1
       grind)
    | exact superpose eq785 eq1150
    | (have j0 := eq1150 X0 X1 X2
       grind)
    | exact resolve eq1150 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1150
  have eq1201 : ∀ X0 X1 : G, (M.op X1 (k (M.op X0 X1) X1)) = X1 ∨ (M.op X1 (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq785 X1 (M.op X0 X1) X0
       have i₂ := eq1120 X1 X0
       grind)
    | exact superpose eq1120 eq785
    | (have j1 := eq1120 X1 X0
       grind)
    | exact resolve eq785 eq1120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq5455 : ∀ X0 X1 X3 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (k (M.op X1 X0) X0) ∨ (M.op X1 X0) = (M.op (M.op X1 X0) (M.op X3 X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1131 X0 X1 (M.op x X0) X3
       have i₂ := eq785 X0 X1 x
       grind)
    | exact superpose eq785 eq1131
    | exact resolve eq1131 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1131
  have eq7142 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq425 x y
       grind)
    | exact superpose eq425 eq16
    | (have j1 := eq425 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq425 x y
       grind)
    | exact resolve eq16 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq7180 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq7142
  have eq7207 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7180
       grind)
    | exact superpose eq7180 eq16
    | exact resolve eq16 eq7180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7216 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op (M.op X0 (σ x)) (M.op X1 (σ y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq783 (σ y) X1 (σ x) x
       have i₂ := eq7180
       grind)
    | exact superpose eq7180 eq783
    | exact resolve eq783 eq7180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7218 : (M.op (σ y) (σ x)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq784 (σ x) (σ y)
       have i₂ := eq7180
       grind)
    | exact superpose eq7180 eq784
    | exact resolve eq784 eq7180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq784
  have eq7219 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq785 (σ y) X0 (σ x)
       have i₂ := eq7180
       grind)
    | exact superpose eq7180 eq785
    | exact resolve eq785 eq7180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7244 : (M.op (σ y) (σ x)) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7218
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq7218
    | exact resolve eq7218 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7218
  have eq7408 : (k (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1160 (σ y) x (σ x)
       have i₂ := eq7219 x
       grind)
    | exact superpose eq7219 eq1160
    | exact resolve eq1160 eq7219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160 eq7219
  have eq7440 : (M.op (σ x) (σ x)) = (σ (k x y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7408
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq7408
    | exact resolve eq7408 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7408
  have eq7445 : (σ x) = (σ (k x y)) ∨ (M.op (σ x) (σ x)) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7440
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq7440
    | exact resolve eq7440 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7440
  have eq7448 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ x)) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq291 eq7445
    | (have j1 := eq291 x y
       grind)
    | exact resolve eq7445 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7445
  have eq7449 : (M.op (σ x) (σ x)) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7448
       have r₂ := eq7207
       grind)
    | exact resolve eq7448 eq7207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7448
  have eq7450 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq291 eq7449
    | (have j1 := eq291 x y
       grind)
    | exact resolve eq7449 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7449
  have eq7453 : (σ y) ≠ (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq685 y x
       have i₂ := eq7244
       grind)
    | exact superpose eq7244 eq685
    | (have j0 := eq685 y x
       grind)
    | exact resolve eq685 eq7244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685 eq7244
  have eq7529 : (σ y) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (σ (k x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7180 eq7453
    | exact resolve eq7453 eq7180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7180 eq7453
  have eq7530 : (σ y) ≠ (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq291 eq7529
    | (have j1 := eq291 x y
       grind)
    | (have r₁ := eq7529
       have r₂ := eq291 (σ y) (σ x)
       grind)
    | exact resolve eq7529 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7529
  have eq7531 : (σ y) ≠ (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7530
       have r₂ := eq7207
       grind)
    | exact resolve eq7530 eq7207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7530
  have eq7581 : (k x x) = (τ (σ (M.op x y))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq444 x x
       have i₂ := eq7450
       grind)
    | exact superpose eq7450 eq444
    | exact resolve eq444 eq7450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444
  have eq7628 : (k x x) = (τ (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7581
       have r₂ := eq7207
       grind)
    | exact resolve eq7581 eq7207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7581
  have eq7635 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7628
       have i₂ := eq10 (M.op x y)
       grind)
    | exact superpose eq10 eq7628
    | exact resolve eq7628 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7628
  have eq8097 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq7216 (σ x) x
       have i₂ := eq7450
       grind)
    | exact superpose eq7450 eq7216
    | exact resolve eq7216 eq7450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7216
  have eq8153 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq8097 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8097
  have eq16383 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 (M.op X1 (M.op X2 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1127 X1 X2 X0 X0
       have i₂ := eq785 X0 X1 X2
       grind)
    | exact superpose eq785 eq1127
    | (have j0 := eq1127 X1 X2 X0 x
       grind)
    | exact resolve eq1127 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq16464 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 (M.op X2 X0))) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq291 eq16383
    | (have j0 := eq16383 X0 X1 X2
       have j1 := eq291 X0 X0
       grind)
    | exact resolve eq16383 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291 eq16383
  have eq16573 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ (M.op X1 (M.op X2 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X1 (M.op X2 X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq292 X0 (M.op X1 (M.op X2 X0))
       have i₂ := eq16464 X0 X1 X2
       grind)
    | exact superpose eq16464 eq292
    | (have j0 := eq292 X0 (M.op X1 (M.op X2 X0))
       have j1 := eq16464 X0 X1 X2
       grind)
    | exact resolve eq292 eq16464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16590 : ∀ X0 X1 X2 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op X2 (σ X0))))) ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28 X0 (M.op X1 (M.op X2 (σ X0)))
       have i₂ := eq16464 (σ X0) X1 X2
       grind)
    | exact superpose eq16464 eq28
    | (have j1 := eq16464 (σ X0) X1 X2
       grind)
    | exact resolve eq28 eq16464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq16635 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (σ (M.op X1 (M.op X2 X0)))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq16573 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16573
  have eq16671 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X2 (σ X0))))) = X0 ∨ (M.op (σ X0) (σ X0)) = (k (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16590 X0 X1 X2
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq16590
    | (have j0 := eq16590 X0 X1 X2
       grind)
    | exact resolve eq16590 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16590
  have eq16738 : ∀ X0 X1 X2 : G, (k X0 (τ (M.op X1 (M.op X2 (σ X0))))) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16671 X0 X1 X2
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq16671
    | (have j0 := eq16671 X0 X1 X2
       grind)
    | exact resolve eq16671 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16671
  have eq16914 : ∀ X0 X1 X2 : G, (σ (M.op X1 (M.op X2 X0))) = (M.op (σ (M.op X1 (M.op X2 X0))) (k (σ X0) (σ (M.op X1 (M.op X2 X0))))) ∨ (σ (M.op X1 (M.op X2 X0))) = (M.op (σ (M.op X1 (M.op X2 X0))) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1201 (σ X0) (σ (M.op X1 (M.op X2 X0)))
       have i₂ := eq16635 X0 X1 X2
       grind)
    | exact superpose eq16635 eq1201
    | (have j1 := eq16635 X0 X1 X2
       grind)
    | exact resolve eq1201 eq16635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq16927 : ∀ X0 X1 X2 : G, (σ (M.op X1 (M.op X2 X0))) = (M.op (σ (M.op X1 (M.op X2 X0))) (σ (k X0 (M.op X1 (M.op X2 X0))))) ∨ (σ (M.op X1 (M.op X2 X0))) = (M.op (σ (M.op X1 (M.op X2 X0))) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16914 X0 X1 X2
       have i₂ := eq15 X0 (M.op X1 (M.op X2 X0))
       grind)
    | exact superpose eq15 eq16914
    | (have j0 := eq16914 X0 X1 X2
       grind)
    | exact resolve eq16914 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16914
  have eq16970 : ∀ X0 X1 X2 : G, (σ (M.op X1 (M.op X2 X0))) = (M.op (σ (M.op X1 (M.op X2 X0))) (σ X0)) ∨ (σ (M.op X1 (M.op X2 X0))) = (M.op (σ (M.op X1 (M.op X2 X0))) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | exact superpose eq16464 eq16927
    | (have j0 := eq16927 X0 X1 X2
       have j1 := eq16464 X0 X1 X2
       grind)
    | exact resolve eq16927 eq16464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16927
  have eq16971 : ∀ X0 X1 X2 : G, (σ (M.op X1 (M.op X2 X0))) = (M.op (σ (M.op X1 (M.op X2 X0))) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq16970 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16970
  have eq17875 : ∀ X0 X1 : G, (k X0 (k X0 (τ (M.op X1 (σ X0))))) = X0 ∨ (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16738 X0 (σ X0) X1
       have i₂ := eq811 X0 X1
       grind)
    | exact superpose eq811 eq16738
    | (have j0 := eq16738 X0 X1 x
       grind)
    | exact resolve eq16738 eq811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811 eq16738
  have eq21700 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (M.op X1 X0)) = (k (M.op X1 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1140 X0 X1 x X0
       have i₂ := eq785 X0 X1 x
       grind)
    | exact superpose eq785 eq1140
    | exact resolve eq1140 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21825 : ∀ X0 X1 : G, (M.op X1 (k (M.op X0 X1) X1)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq785 X1 (M.op X0 X1) X0
       have i₂ := eq21700 X1 X0
       grind)
    | exact superpose eq21700 eq785
    | (have j1 := eq21700 X1 X1
       grind)
    | exact resolve eq785 eq21700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22125 : (σ x) = (M.op (σ x) (k (σ (M.op x y)) (σ x))) ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21825 (σ x) (σ x)
       have i₂ := eq7450
       grind)
    | exact superpose eq7450 eq21825
    | exact resolve eq21825 eq7450
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7450 eq21825
  have eq22226 : (σ x) = (M.op (σ x) (k (σ (M.op x y)) (σ x))) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22125
       have r₂ := eq7207
       grind)
    | exact resolve eq22125 eq7207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7207 eq22125
  have eq22248 : (σ x) = (M.op (σ x) (σ (k (M.op x y) x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22226
       have i₂ := eq15 (M.op x y) x
       grind)
    | exact superpose eq15 eq22226
    | exact resolve eq22226 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22226
  have eq29224 : ∀ X0 X1 X2 : G, (k X2 (k X2 (τ (σ (M.op X0 (M.op X1 X2)))))) = X2 ∨ (M.op (σ X2) (σ X2)) = (σ (k X2 X2)) ∨ (M.op X2 X2) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq17875 X2 (σ (M.op X0 (M.op X1 X2)))
       have i₂ := eq16971 X2 X0 X1
       grind)
    | exact superpose eq16971 eq17875
    | (have j0 := eq17875 X2 X1
       have j1 := eq16971 X2 X1 X2
       grind)
    | exact resolve eq17875 eq16971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17875
  have eq29263 : ∀ X0 X1 X2 X3 : G, (σ X2) = (M.op (σ X2) (M.op X3 (σ (M.op X0 (M.op X1 X2))))) ∨ (M.op X2 X2) = (k X2 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq785 (σ X2) X3 (σ (M.op X0 (M.op X1 X2)))
       have i₂ := eq16971 X2 X0 X1
       grind)
    | exact superpose eq16971 eq785
    | (have j1 := eq16971 X2 X1 X2
       grind)
    | exact resolve eq785 eq16971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16971
  have eq29356 : ∀ X0 X1 X2 : G, (k X2 (k X2 (M.op X0 (M.op X1 X2)))) = X2 ∨ (M.op (σ X2) (σ X2)) = (σ (k X2 X2)) ∨ (M.op X2 X2) = (k X2 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq29224 X0 X1 X2
       have i₂ := eq10 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq10 eq29224
    | (have j0 := eq29224 X0 X1 X2
       grind)
    | exact resolve eq29224 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29224
  have eq29426 : ∀ X2 : G, (k X2 X2) = X2 ∨ (M.op (σ X2) (σ X2)) = (σ (k X2 X2)) ∨ (M.op X2 X2) = (k X2 X2) := by
    intro X2
    first
    | exact superpose eq16464 eq29356
    | (have j0 := eq29356 x x X2
       have j1 := eq16464 X2 x X2
       grind)
    | exact resolve eq29356 eq16464
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16464 eq29356
  have eq29459 : ∀ X2 : G, (M.op (σ X2) (σ X2)) = (σ (k X2 X2)) ∨ (M.op X2 X2) = (k X2 X2) := by
    intro X2
    first
    | (have j0 := eq29426 X2
       have j1 := eq671 X2 X2
       grind)
    | (have r₁ := eq29426 x
       have r₂ := eq671 x x
       grind)
    | exact resolve eq29426 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29426
  have eq29486 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq29459 X0
       grind)
    | exact superpose eq29459 eq10
    | (have j1 := eq29459 X0
       grind)
    | exact resolve eq10 eq29459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29459
  have eq30643 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq29263 x x X0 (σ X0)
       have i₂ := eq16635 X0 x x
       grind)
    | exact superpose eq16635 eq29263
    | (have j0 := eq29263 X0 x X0 x
       have j1 := eq16635 X0 x x
       grind)
    | exact resolve eq29263 eq16635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16635 eq29263
  have eq30756 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq30643 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30643
  have eq30886 : ∀ X0 : G, (τ (σ X0)) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | exact superpose eq30756 eq29486
    | (have j0 := eq29486 X0
       have j1 := eq30756 X0
       grind)
    | exact resolve eq29486 eq30756
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29486 eq30756
  have eq31071 : ∀ X0 : G, (k X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq30886 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq30886
    | (have j0 := eq30886 X0
       grind)
    | exact resolve eq30886 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30886
  have eq31099 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq31071 X0
       have j1 := eq671 X0 X0
       grind)
    | (have r₁ := eq31071 x
       have r₂ := eq671 x x
       grind)
    | exact resolve eq31071 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671 eq31071
  have eq31135 : (M.op x y) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7635
       have i₂ := eq31099 x
       grind)
    | exact superpose eq31099 eq7635
    | exact resolve eq7635 eq31099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7635
  have eq31198 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq31099 (σ X0)
       grind)
    | exact superpose eq31099 eq15
    | exact resolve eq15 eq31099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31219 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq31099 (τ X0)
       grind)
    | exact superpose eq31099 eq31
    | exact resolve eq31 eq31099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq31256 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31219 X0
       have i₂ := eq31099 X0
       grind)
    | exact superpose eq31099 eq31219
    | exact resolve eq31219 eq31099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31219
  have eq31277 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq31198 X0
       have i₂ := eq31099 X0
       grind)
    | exact superpose eq31099 eq31198
    | exact resolve eq31198 eq31099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31099 eq31198
  have eq31488 : ∀ X0 X1 : G, (τ X0) = (M.op (τ X0) (M.op X1 (τ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq785 (τ X0) X1 (τ X0)
       have i₂ := eq31256 X0
       grind)
    | exact superpose eq31256 eq785
    | exact resolve eq785 eq31256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31684 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (σ X0))) = (M.op (M.op X1 (M.op X2 (σ X0))) (σ (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq783 (σ X0) X1 X2 (σ X0)
       have i₂ := eq31277 X0
       grind)
    | exact superpose eq31277 eq783
    | exact resolve eq783 eq31277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31826 : ∀ X0 : G, (σ (M.op x x)) = (M.op (σ (M.op x x)) (M.op X0 (σ y))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq31135 eq8153
    | exact resolve eq8153 eq31135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8153
  have eq31829 : (σ x) = (M.op (σ x) (σ (k (M.op x x) x))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31135 eq22248
    | exact resolve eq22248 eq31135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22248
  have eq31849 : ∀ X0 : G, y = (M.op y (M.op X0 (M.op x x))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq785 y X0 x
       have i₂ := eq31135
       grind)
    | exact superpose eq31135 eq785
    | exact resolve eq785 eq31135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31902 : x ≠ (M.op x x) ∨ x = (M.op x y) := by grind
  clear eq31135
  have eq32186 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq31488 X0 (τ (M.op X0 X0))
       have i₂ := eq31256 (M.op X0 X0)
       grind)
    | exact superpose eq31256 eq31488
    | exact resolve eq31488 eq31256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31256 eq31488
  have eq32793 : ∀ X0 X1 : G, y = (M.op y (M.op X0 (M.op X1 x))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq31849 (M.op X0 (M.op X1 x))
       have i₂ := eq783 x X0 X1 x
       grind)
    | exact superpose eq783 eq31849
    | exact resolve eq31849 eq783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq783 eq31849
  have eq32939 : ∀ X0 : G, (M.op (M.op X0 x) (M.op X0 x)) = (k (M.op X0 x) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2⟩ := hcon
    have f32939_14 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) (M.op X2 X3)) = (k (M.op X2 X3) (M.op X0 (M.op X1 (M.op X2 X3)))) ∨ (M.op X3 (M.op X0 (M.op X1 (M.op X2 X3)))) = X3 := by
      intro X0 X1 X2 X3
      grind
    have f32939_15 : ∀ X0 X1 : G, y = (M.op y (M.op X0 (M.op X1 x))) ∨ x = (M.op x y) := by
      intro X0 X1
      grind
    have f32939_24 : (M.op (M.op X0 x) (M.op X0 x)) ≠ (k (M.op X0 x) y) := by grind
    have f32939_26 : x ≠ (M.op x y) := by grind
    have f32939_27 : ∀ X0 X1 : G, y = (M.op y (M.op X0 (M.op X1 x))) := by
      intro X0 X1
      first
      | (have j0 := f32939_15 X0 X1
         grind)
      | (have r₁ := f32939_15 X0 X1
         have r₂ := f32939_26
         grind)
      | exact resolve f32939_15 f32939_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f32939_105 : ∀ X0 : G, (k (M.op X0 x) y) = (M.op (M.op X0 x) (M.op X0 x)) ∨ x = (M.op x y) := by
      intro X0
      first
      | (have i₁ := f32939_14 y X0 x x
         have i₂ := f32939_27 X0 x
         grind)
      | exact superpose f32939_27 f32939_14
      | exact resolve f32939_14 f32939_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f32939_109 : ∀ X0 : G, (k (M.op X0 x) y) = (M.op (M.op X0 x) (M.op X0 x)) := by
      intro X0
      first
      | (have j0 := f32939_105 X0
         grind)
      | (have r₁ := f32939_105 X0
         have r₂ := f32939_26
         grind)
      | exact resolve f32939_105 f32939_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f32939_133 : (k (M.op X0 x) y) ≠ (k (M.op X0 x) y) := by
      first
      | (have i₁ := f32939_24
         have i₂ := f32939_109 X0
         grind)
      | exact superpose f32939_109 f32939_24
      | (have r₁ := f32939_24
         have r₂ := f32939_109 X0
         grind)
      | exact resolve f32939_24 f32939_109
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f32939_142 : False := by grind
    exact f32939_142
  clear eq32793
  have eq33031 : ∀ X0 : G, (M.op (M.op X0 x) (M.op X0 x)) = (k (M.op X0 x) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq32939 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32939
  have eq43869 : ∀ X0 : G, (k (M.op X0 x) x) = (k (M.op X0 x) y) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq21700 x X0
       have i₂ := eq33031 X0
       grind)
    | exact superpose eq33031 eq21700
    | (have j0 := eq21700 x x
       grind)
    | exact resolve eq21700 eq33031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21700 eq33031
  have eq44047 : ∀ X0 : G, (k (M.op X0 x) x) = (k (M.op X0 x) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq43869 X0
       grind)
    | (have r₁ := eq43869 X0
       have r₂ := eq31902
       grind)
    | exact resolve eq43869 eq31902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31902 eq43869
  have eq54441 : (M.op (σ (M.op x x)) (σ y)) = (k (σ (M.op x x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq782 (σ y) (σ (M.op x x)) x
       have i₂ := eq31826 x
       grind)
    | exact superpose eq31826 eq782
    | exact resolve eq782 eq31826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31826
  have eq54575 : (M.op (σ (M.op x x)) (σ y)) = (σ (k (M.op x x) y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq54441
       have i₂ := eq15 (M.op x x) y
       grind)
    | exact superpose eq15 eq54441
    | exact resolve eq54441 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54441
  have eq54600 : (M.op (σ (M.op x x)) (σ y)) = (σ (k (M.op x x) x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44047 eq54575
    | exact resolve eq54575 eq44047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44047 eq54575
  have eq54714 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ (k (M.op x x) x)))) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq785 (σ y) X0 (σ (M.op x x))
       have i₂ := eq54600
       grind)
    | exact superpose eq54600 eq785
    | exact resolve eq785 eq54600
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54600
  have eq54902 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq54714 (σ x)
       have i₂ := eq31829
       grind)
    | exact superpose eq31829 eq54714
    | exact resolve eq54714 eq31829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31829 eq54714
  have eq55012 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq54902
  have eq55044 : x = (M.op x y) := by
    first
    | (have r₁ := eq55012
       have r₂ := eq7531
       grind)
    | exact resolve eq55012 eq7531
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7531 eq55012
  have eq55080 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq55044
       grind)
    | exact superpose eq55044 eq16
    | exact resolve eq16 eq55044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55090 : ∀ X0 : G, (M.op (M.op X0 x) y) = (k (M.op X0 x) y) := by
    intro X0
    first
    | (have i₁ := eq782 y x x
       have i₂ := eq55044
       grind)
    | exact superpose eq55044 eq782
    | exact resolve eq782 eq55044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq55137 : ∀ X0 : G, x = (M.op x (M.op X0 y)) ∨ (k x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq5455 y x x
       have i₂ := eq55044
       grind)
    | exact superpose eq55044 eq5455
    | exact resolve eq5455 eq55044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5455
  have eq56130 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq825 x x y
       have i₂ := eq55137 x
       grind)
    | exact superpose eq55137 eq825
    | exact resolve eq825 eq55137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55137
  have eq56246 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq56130
       have r₂ := eq55080
       grind)
    | exact resolve eq56130 eq55080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56130
  have eq56253 : (σ x) = (M.op (σ x) (σ y)) ∨ (k x y) = (M.op x x) := by
    first
    | (have i₁ := eq56246
       have i₂ := eq55044
       grind)
    | exact superpose eq55044 eq56246
    | exact resolve eq56246 eq55044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56246
  have eq56254 : (k x y) = (M.op x x) := by
    first
    | (have r₁ := eq56253
       have r₂ := eq55080
       grind)
    | exact resolve eq56253 eq55080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56253
  have eq56259 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq292 x y
       have i₂ := eq56254
       grind)
    | exact superpose eq56254 eq292
    | (have j0 := eq292 x y
       grind)
    | exact resolve eq292 eq56254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq292
  have eq56264 : (σ x) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq594 x y
       have i₂ := eq56254
       grind)
    | exact superpose eq56254 eq594
    | (have j0 := eq594 x y
       grind)
    | exact resolve eq594 eq56254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594 eq56254
  have eq56279 : (σ x) ≠ (σ (M.op x x)) := by
    first
    | (have r₁ := eq56264
       have r₂ := eq55080
       grind)
    | exact resolve eq56264 eq55080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56264
  have eq56281 : (M.op (σ x) (σ y)) = (σ (M.op x x)) := by
    first
    | (have r₁ := eq56259
       have r₂ := eq55080
       grind)
    | exact resolve eq56259 eq55080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56259
  have eq56316 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op X0 (σ (M.op x x)))) := by
    intro X0
    first
    | (have i₁ := eq785 (σ y) X0 (σ x)
       have i₂ := eq56281
       grind)
    | exact superpose eq56281 eq785
    | exact resolve eq785 eq56281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785
  have eq56677 : ∀ X0 X1 : G, (σ y) = (M.op (σ y) (M.op X0 (M.op X1 (σ x)))) := by
    intro X0 X1
    first
    | (have i₁ := eq56316 (M.op X0 (M.op X1 (σ x)))
       have i₂ := eq31684 x X0 X1
       grind)
    | exact superpose eq31684 eq56316
    | exact resolve eq56316 eq31684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31684 eq56316
  have eq56893 : ∀ X0 : G, (k (M.op X0 (σ x)) (σ y)) = (M.op (M.op X0 (σ x)) (M.op X0 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq1140 (σ y) X0 x (σ x)
       have i₂ := eq56677 X0 x
       grind)
    | exact superpose eq56677 eq1140
    | exact resolve eq1140 eq56677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140 eq56677
  have eq57015 : ∀ X0 : G, (σ x) = (σ (M.op x x)) ∨ (k (M.op X0 (σ x)) (σ y)) = (M.op (M.op X0 (σ x)) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have i₁ := eq56893 X0
       have i₂ := eq56281
       grind)
    | exact superpose eq56281 eq56893
    | (have j0 := eq56893 X0
       grind)
    | exact resolve eq56893 eq56281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56893
  have eq57027 : ∀ X0 : G, (k (M.op X0 (σ x)) (σ y)) = (M.op (M.op X0 (σ x)) (M.op X0 (σ x))) := by
    intro X0
    first
    | (have j0 := eq57015 X0
       grind)
    | (have r₁ := eq57015 X0
       have r₂ := eq56279
       grind)
    | exact resolve eq57015 eq56279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57015
  have eq64663 : (τ (σ x)) = (M.op (τ (σ x)) (τ (k (M.op (σ x) (σ x)) (σ y)))) := by
    first
    | (have i₁ := eq32186 (σ x)
       have i₂ := eq57027 (σ x)
       grind)
    | exact superpose eq57027 eq32186
    | exact resolve eq32186 eq57027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32186 eq57027
  have eq64879 : (τ (σ x)) = (M.op (τ (σ x)) (k (τ (M.op (σ x) (σ x))) y)) := by
    first
    | (have i₁ := eq64663
       have i₂ := eq22 (M.op (σ x) (σ x)) y
       grind)
    | exact superpose eq22 eq64663
    | exact resolve eq64663 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq64663
  have eq64907 : (τ (σ x)) = (M.op (τ (σ x)) (k (τ (σ (M.op x x))) y)) := by
    first
    | (have i₁ := eq64879
       have i₂ := eq31277 x
       grind)
    | exact superpose eq31277 eq64879
    | exact resolve eq64879 eq31277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31277 eq64879
  have eq64925 : (τ (σ x)) = (M.op (τ (σ x)) (k (M.op x x) y)) := by
    first
    | (have i₁ := eq64907
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq64907
    | exact resolve eq64907 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64907
  have eq64937 : (τ (σ x)) = (M.op (τ (σ x)) (M.op (M.op x x) y)) := by
    first
    | (have i₁ := eq64925
       have i₂ := eq55090 x
       grind)
    | exact superpose eq55090 eq64925
    | exact resolve eq64925 eq55090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55090 eq64925
  have eq64939 : x = (M.op x (M.op (M.op x x) y)) := by
    first
    | (have i₁ := eq64937
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq64937
    | exact resolve eq64937 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64937
  have eq64954 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq825 x (M.op x x) y
       have i₂ := eq64939
       grind)
    | exact superpose eq64939 eq825
    | exact resolve eq825 eq64939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq825 eq64939
  have eq65070 : (σ (M.op x y)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq64954
       have i₂ := eq56281
       grind)
    | exact superpose eq56281 eq64954
    | exact resolve eq64954 eq56281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56281 eq64954
  have eq65077 : (σ x) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq65070
       have i₂ := eq55044
       grind)
    | exact superpose eq55044 eq65070
    | exact resolve eq65070 eq55044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55044 eq65070
  have eq65082 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq65077
       have r₂ := eq56279
       grind)
    | exact resolve eq65077 eq56279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56279 eq65077
  have eq65083 : False := by grind
  exact eq65083

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxx_y_pyx_x_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
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
  clear eq18
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
  have eq62 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
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
  have eq93 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
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
  have eq395 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X1 (σ X0)
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq93
    | (have j0 := eq93 X1 (σ X0)
       grind)
    | (have r₁ := eq93 X0 (σ X0)
       have r₂ := eq78 X0
       grind)
    | exact resolve eq93 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq400 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq395 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq395
    | (have j0 := eq395 X0 X1
       grind)
    | exact resolve eq395 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq525 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq550 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq525 X0 X1
       have i₂ := eq78 X1
       grind)
    | exact superpose eq78 eq525
    | (have j0 := eq525 X0 X1
       grind)
    | exact resolve eq525 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq572 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq550 X0 X1
       have i₂ := eq78 X1
       grind)
    | exact superpose eq78 eq550
    | (have j0 := eq550 X0 X1
       grind)
    | exact resolve eq550 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550
  have eq578 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq572 X0 X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq572
    | (have j0 := eq572 X0 X1
       grind)
    | exact resolve eq572 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq582 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq578 X0 X1
       have j1 := eq400 X1 X0
       grind)
    | (have r₁ := eq578 X0 X1
       have r₂ := eq400 X0 X1
       grind)
    | (have r₁ := eq578 X1 X0
       have r₂ := eq400 X0 X1
       grind)
    | (have r₁ := eq578 (M.op X0 X0) X1
       have r₂ := eq400 X0 X1
       grind)
    | exact resolve eq578 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq578
  have eq585 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq582 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq582
    | exact resolve eq582 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq582 x y
       grind)
    | exact superpose eq582 eq16
    | (have j1 := eq582 x y
       grind)
    | exact resolve eq16 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq631 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq585 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq585
    | (have j0 := eq585 X0 X1
       grind)
    | exact resolve eq585 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq585
  have eq664 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq700 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 x
       have i₂ := eq664 X1 x X0
       grind)
    | exact superpose eq664 eq9
    | exact resolve eq9 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X0 (M.op X2 X0) X2
       have i₂ := eq664 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq664 eq63
    | exact resolve eq63 eq664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq720 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq711 X0 X1 X2
       have i₂ := eq63 X0 X0 X1
       grind)
    | exact superpose eq63 eq711
    | exact resolve eq711 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq711
  have eq754 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq700 X0 (M.op X0 X0)
       have i₂ := eq700 X0 X0
       grind)
    | exact superpose eq700 eq700
    | exact resolve eq700 eq700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq700
  have eq768 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq754 (σ X0)
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq754
    | exact resolve eq754 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq1006 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 X1) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq754 X1
       have i₂ := eq720 X1 X0 X1
       grind)
    | (have i₁ := eq754 X1
       have i₂ := eq720 X1 X1 X0
       grind)
    | exact superpose eq720 eq754
    | exact resolve eq754 eq720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720 eq754
  have eq5443 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq631 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq631
    | (have j0 := eq631 X1 (τ X0)
       grind)
    | exact resolve eq631 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631
  have eq5476 : ∀ X0 X1 : G, (σ (τ (M.op X0 X0))) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq5443 X0 X1
       have i₂ := eq76 X0
       grind)
    | exact superpose eq76 eq5443
    | (have j0 := eq5443 X0 X1
       grind)
    | exact resolve eq5443 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq5443
  have eq5477 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5476 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq5476
    | (have j0 := eq5476 X0 X1
       grind)
    | exact resolve eq5476 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5476
  have eq76377 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq594
       have i₂ := eq5477 y x
       grind)
    | exact superpose eq5477 eq594
    | (have j1 := eq5477 y x
       grind)
    | exact resolve eq594 eq5477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594 eq5477
  have eq76380 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq76377
  have eq76397 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq76380
       grind)
    | exact superpose eq76380 eq10
    | exact resolve eq10 eq76380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76380
  have eq76494 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq76397
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq76397
    | exact resolve eq76397 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76397
  have eq76495 : x = (M.op y y) := by grind
  clear eq76494
  have eq76538 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq768 y
       have i₂ := eq76495
       grind)
    | exact superpose eq76495 eq768
    | exact resolve eq768 eq76495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq76624 : x = (M.op x y) := by
    first
    | (have i₁ := eq1006 y y
       have i₂ := eq76495
       grind)
    | exact superpose eq76495 eq1006
    | exact resolve eq1006 eq76495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006 eq76495
  have eq78041 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq76538
       grind)
    | exact superpose eq76538 eq16
    | exact resolve eq16 eq76538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76538
  have eq78240 : (σ x) ≠ (σ x) := by
    first
    | (have i₁ := eq78041
       have i₂ := eq76624
       grind)
    | exact superpose eq76624 eq78041
    | exact resolve eq78041 eq76624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76624 eq78041
  have eq78241 : False := by grind
  exact eq78241

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then X else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxx_pyx_x_pxx_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq24 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq24
    | exact resolve eq24 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (τ (σ X0)) = (k X0 (τ (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  have eq67 : ∀ X0 : G, (k X0 (τ (M.op (σ X0) (σ X0)))) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq56
    | exact resolve eq56 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq94 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq549 (τ X0)
       grind)
    | exact superpose eq549 eq18
    | (have j1 := eq549 (τ X0)
       grind)
    | exact resolve eq18 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq549
  have eq572 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq567 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq567
    | (have j0 := eq567 X0
       grind)
    | exact resolve eq567 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq642 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq572 X0
       grind)
    | exact superpose eq572 eq10
    | (have j1 := eq572 X0
       grind)
    | exact resolve eq10 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq750 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq1057 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op X4 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))))) = (M.op X5 (M.op X5 (M.op (M.op X4 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2)))) (M.op X3 (M.op (M.op X0 (M.op (M.op X1 X2) X2)) (M.op X4 (M.op X2 (M.op X0 (M.op (M.op X1 X2) X2))))))))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq94 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0)))) X1 X2 X1
       have i₂ := eq94 X0 X1 X2 X3
       grind)
    | exact superpose eq94 eq94
    | exact resolve eq94 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1065 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 X0)) = (M.op X0 (M.op (M.op X1 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq94 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq94
    | exact resolve eq94 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1083 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X3 X0))) = (M.op (M.op X3 X0) (M.op (M.op X0 (M.op (M.op X1 X0) X0)) (M.op X3 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1065 (M.op X3 X0) X3 X2
       have i₂ := eq1065 X0 X1 X3
       grind)
    | exact superpose eq1065 eq1065
    | exact resolve eq1065 eq1065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1087 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1065 X1 x X0
       have i₂ := eq1065 X1 x X2
       grind)
    | exact superpose eq1065 eq1065
    | exact resolve eq1065 eq1065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1089 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq95 X0 (M.op X2 X0) X2
       have i₂ := eq1065 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq1065 eq95
    | exact resolve eq95 eq1065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1099 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 x
       have i₂ := eq1065 X1 x X0
       grind)
    | exact superpose eq1065 eq9
    | exact resolve eq9 eq1065
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1065
  have eq1103 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1089 X0 X1 X2
       have i₂ := eq95 X0 X0 X1
       grind)
    | exact superpose eq95 eq1089
    | exact resolve eq1089 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1089
  have eq1118 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1099 X0 (M.op X0 X0)
       have i₂ := eq1099 X0 X0
       grind)
    | exact superpose eq1099 eq1099
    | exact resolve eq1099 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1123 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq95 (M.op X0 (M.op X0 X1)) X1 X1
       have i₂ := eq1099 X0 X1
       grind)
    | exact superpose eq1099 eq95
    | exact resolve eq95 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1126 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1123 X1 X0 X2
       have i₂ := eq1099 X0 X1
       grind)
    | exact superpose eq1099 eq1123
    | exact resolve eq1123 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1123
  have eq1134 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq1118 X0
       grind)
    | exact superpose eq1118 eq9
    | exact resolve eq9 eq1118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1168 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1087 X1 (M.op X1 (M.op X0 X0)) X2
       have i₂ := eq1134 X0 X1
       grind)
    | exact superpose eq1134 eq1087
    | exact resolve eq1087 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1174 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1087 X0 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq1099 X1 X0
       grind)
    | exact superpose eq1099 eq1087
    | exact resolve eq1087 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1223 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op (M.op X2 X1) (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1099 X2 (M.op X2 X1)
       have i₂ := eq1087 X2 X1 X0
       grind)
    | (have i₁ := eq1099 X2 (M.op X2 X1)
       have i₂ := eq1087 X0 X1 X2
       grind)
    | exact superpose eq1087 eq1099
    | exact resolve eq1099 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1264 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1103 X0 X1 X0
       have i₂ := eq1118 X0
       grind)
    | exact superpose eq1118 eq1103
    | exact resolve eq1103 eq1118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1103 eq1118
  have eq1330 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq94 X0 X1 X2 X1
       have i₂ := eq1264 X0 X1
       grind)
    | exact superpose eq1264 eq94
    | exact resolve eq94 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq1331 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq95 X0 X1 X1
       have i₂ := eq1264 X0 X1
       grind)
    | exact superpose eq1264 eq95
    | exact resolve eq95 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq1352 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1331 X1 X1
       have i₂ := eq1087 X1 X1 X0
       grind)
    | (have i₁ := eq1331 X1 X1
       have i₂ := eq1087 X0 X1 X1
       grind)
    | exact superpose eq1087 eq1331
    | exact resolve eq1331 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1331
  have eq1428 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))) = (M.op (M.op (M.op X2 X0) X0) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1352 (M.op X2 X0) (M.op X1 (M.op X1 X0))
       have i₂ := eq1126 X0 X1 X2
       grind)
    | exact superpose eq1126 eq1352
    | exact resolve eq1352 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1352
  have eq1448 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1428 X0 X1 x
       have i₂ := eq1126 X0 X1 (M.op x X0)
       grind)
    | exact superpose eq1126 eq1428
    | exact resolve eq1428 eq1126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1126 eq1428
  have eq1572 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1174 (M.op X1 X0) X1 X1
       have i₂ := eq1174 X0 X1 X1
       grind)
    | exact superpose eq1174 eq1174
    | exact resolve eq1174 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1621 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 X0)) = (M.op X3 (M.op X3 (M.op X1 (M.op X2 (M.op X2 X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1087 X1 (M.op X1 (M.op X2 (M.op X2 X0))) X3
       have i₂ := eq1174 X0 X2 X1
       grind)
    | exact superpose eq1174 eq1087
    | exact resolve eq1087 eq1174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1174
  have eq1880 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (k (M.op X1 (M.op X1 X0)) X0) := by
    intro X0 X1
    grind
  clear eq1448
  have eq2307 : ∀ X0 X1 X2 : G, (M.op (σ X0) (σ X1)) ≠ (M.op X2 (σ X1)) ∨ (M.op (σ X0) (σ X1)) = X2 ∨ (k (σ X1) X2) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq750 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq750 X0 X0
       grind)
    | exact superpose eq750 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq750 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq750 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq750 X0 X0
       grind)
    | exact resolve eq13 eq750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2344 : ∀ X0 X1 : G, (σ X1) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq750 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750
  have eq2475 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) = (M.op (M.op X1 (M.op X0 (M.op X1 X1))) (M.op X1 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1168 (M.op X1 (M.op X0 (M.op X1 X1))) (M.op X1 (M.op X0 (M.op X1 X1))) X2
       have i₂ := eq1330 X1 (M.op X1 (M.op X0 (M.op X1 X1))) X0
       grind)
    | exact superpose eq1330 eq1168
    | exact resolve eq1168 eq1330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2507 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op X1 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1330 X1 X1 X0
       have i₂ := eq1168 X1 X0 X1
       grind)
    | exact superpose eq1168 eq1330
    | exact resolve eq1330 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1330
  have eq2575 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) = (M.op X1 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2475 X0 X1 X2
       have i₂ := eq1572 (M.op X0 (M.op X1 X1)) X1
       grind)
    | exact superpose eq1572 eq2475
    | exact resolve eq2475 eq1572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2475
  have eq2600 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) = (M.op X1 (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2575 X0 X1 X2
       have i₂ := eq1572 (M.op X1 X1) X0
       grind)
    | exact superpose eq1572 eq2575
    | exact resolve eq2575 eq1572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2575
  have eq2610 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) = (M.op X1 (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2600 X0 X1 X2
       have i₂ := eq1572 X1 X1
       grind)
    | exact superpose eq1572 eq2600
    | exact resolve eq2600 eq1572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2600
  have eq2611 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq2610 X0 X1 x
       have i₂ := eq1168 X1 X0 x
       grind)
    | exact superpose eq1168 eq2610
    | exact resolve eq2610 eq1168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1168 eq2610
  have eq3077 : ∀ X0 X1 : G, (τ (M.op X0 (M.op X0 (σ X1)))) = (k (τ (M.op X0 (M.op X0 (σ X1)))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq24 (M.op X0 (M.op X0 (σ X1))) X1
       have i₂ := eq1880 (σ X1) X0
       grind)
    | exact superpose eq1880 eq24
    | exact resolve eq24 eq1880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq3829 : ∀ X0 X1 X2 : G, (M.op X2 X1) = (M.op X1 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2611 X2 X1
       have i₂ := eq1087 X1 X1 X0
       grind)
    | (have i₁ := eq2611 X2 X1
       have i₂ := eq1087 X0 X1 X1
       grind)
    | exact superpose eq1087 eq2611
    | exact resolve eq2611 eq1087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2611
  have eq8889 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1223 X0 (M.op X0 X0) X1
       have i₂ := eq1099 X0 X0
       grind)
    | exact superpose eq1099 eq1223
    | exact resolve eq1223 eq1099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq37798 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq2307 X0 X1 (σ X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2307
  have eq37800 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq37798 X0 X1
       have j1 := eq2344 X1 X0
       grind)
    | (have r₁ := eq37798 X1 X0
       have r₂ := eq2344 X0 X1
       grind)
    | (have r₁ := eq37798 X0 X0
       have r₂ := eq2344 X0 X0
       grind)
    | exact resolve eq37798 eq2344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2344 eq37798
  have eq37825 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq37800 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq37800
    | (have j0 := eq37800 X0 X1
       grind)
    | exact resolve eq37800 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37800
  have eq37826 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq37825 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37825
  have eq37833 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq37826 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37826
  have eq37834 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq37833 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37833
  have eq38700 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq38721 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq37834 (τ X1) (τ X0)
       have i₂ := eq34 X1 X0
       grind)
    | exact superpose eq34 eq37834
    | (have j0 := eq37834 (τ X1) (τ X0)
       grind)
    | exact resolve eq37834 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38767 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq38721 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq38721
    | (have j0 := eq38721 X0 X1
       grind)
    | exact resolve eq38721 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38721
  have eq38788 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq38767 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq38767
    | (have j0 := eq38767 X0 X1
       grind)
    | exact resolve eq38767 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38767
  have eq38797 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (σ (τ X1)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq38788 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq38788
    | (have j0 := eq38788 X0 X1
       grind)
    | exact resolve eq38788 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38788
  have eq38804 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (τ X1)) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq38797 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq38797
    | (have j0 := eq38797 X0 X1
       grind)
    | exact resolve eq38797 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38797
  have eq38809 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq38804 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq38804
    | (have j0 := eq38804 X0 X1
       grind)
    | exact resolve eq38804 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38804
  have eq38839 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37834 X0 X1
       have i₂ := eq38809 X1 X0
       grind)
    | exact superpose eq38809 eq37834
    | (have j0 := eq37834 X0 X1
       have j1 := eq38809 (σ X1) (σ X0)
       grind)
    | exact resolve eq37834 eq38809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38870 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (M.op X0 (σ X1))) ∨ (M.op (σ X1) (σ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq31 X1 X0
       have i₂ := eq38809 (σ X1) X0
       grind)
    | exact superpose eq38809 eq31
    | (have j1 := eq38809 (σ X1) X0
       grind)
    | exact resolve eq31 eq38809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45166 : ∀ X0 X2 X3 X4 X5 : G, (M.op X3 (M.op (M.op X0 (M.op X2 X2)) (M.op X4 (M.op X2 (M.op X0 (M.op X2 X2)))))) = (M.op X5 (M.op X5 (M.op (M.op X4 (M.op X2 (M.op X0 (M.op X2 X2)))) (M.op X3 (M.op (M.op X0 (M.op X2 X2)) (M.op X4 (M.op X2 (M.op X0 (M.op X2 X2))))))))) := by
    intro X0 X2 X3 X4 X5
    first
    | (have i₁ := eq1057 X0 x X0 X3 X4 X5
       have i₂ := eq1264 X0 x
       grind)
    | exact superpose eq1264 eq1057
    | exact resolve eq1057 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1057
  have eq58944 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op X0 (M.op (M.op X1 (M.op X2 (M.op X1 X1))) (M.op X1 (M.op X2 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq45166 X2 X1 X0 (M.op X2 (M.op X1 X1)) (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X2 (M.op X1 X1))))
       have i₂ := eq1621 (M.op X1 (M.op X2 (M.op X1 X1))) X0 (M.op X2 (M.op X1 X1)) (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X2 (M.op X1 X1))))
       grind)
    | exact superpose eq1621 eq45166
    | exact resolve eq45166 eq1621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1621 eq45166
  have eq59111 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op X0 (M.op X1 (M.op (M.op X2 (M.op X1 X1)) (M.op X2 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58944 X0 X1 X2
       have i₂ := eq1572 (M.op X2 (M.op X1 X1)) X1
       grind)
    | exact superpose eq1572 eq58944
    | exact resolve eq58944 eq1572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58944
  have eq59867 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op X0 (M.op X1 (M.op X2 (M.op (M.op X1 X1) (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59111 X0 X1 X2
       have i₂ := eq1572 (M.op X1 X1) X2
       grind)
    | exact superpose eq1572 eq59111
    | exact resolve eq59111 eq1572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59111
  have eq60311 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op X0 (M.op X1 (M.op X2 (M.op X1 (M.op (M.op X1 X1) X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59867 X0 X1 X2
       have i₂ := eq2507 (M.op X1 X1) X1
       grind)
    | exact superpose eq2507 eq59867
    | exact resolve eq59867 eq2507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59867
  have eq60590 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op X0 (M.op X1 (M.op X2 (M.op X1 (M.op X1 X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60311 X0 X1 X2
       have i₂ := eq1264 X1 X1
       grind)
    | exact superpose eq1264 eq60311
    | exact resolve eq60311 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60311
  have eq60758 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 (M.op X1 X1)) (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X2 (M.op X1 X1)))))) = (M.op (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X2 (M.op X1 X1)))) (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60590 X0 X1 X2
       have i₂ := eq3829 X1 X1 X2
       grind)
    | exact superpose eq3829 eq60590
    | exact resolve eq60590 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60590
  have eq60823 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op (M.op X2 (M.op X1 X1)) (M.op X2 (M.op X1 X1)))))) = (M.op (M.op X1 (M.op (M.op X2 (M.op X1 X1)) (M.op X2 (M.op X1 X1)))) (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60758 X0 X0 X2
       have i₂ := eq2507 X0 (M.op X2 (M.op X0 X0))
       grind)
    | exact superpose eq2507 eq60758
    | exact resolve eq60758 eq2507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60758
  have eq60852 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X2 (M.op (M.op X1 X1) (M.op X1 X1)))))) = (M.op (M.op X1 (M.op X2 (M.op (M.op X1 X1) (M.op X1 X1)))) (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60823 X0 X1 X1
       have i₂ := eq1572 (M.op X1 X1) X1
       grind)
    | exact superpose eq1572 eq60823
    | exact resolve eq60823 eq1572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1572 eq60823
  have eq60869 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X2 (M.op X1 (M.op (M.op X1 X1) X1)))))) = (M.op (M.op X1 (M.op X2 (M.op X1 (M.op (M.op X1 X1) X1)))) (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60852 X0 X1 X2
       have i₂ := eq2507 (M.op X1 X1) X1
       grind)
    | exact superpose eq2507 eq60852
    | exact resolve eq60852 eq2507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2507 eq60852
  have eq60882 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 (M.op X1 X1)) (M.op X1 (M.op X2 (M.op X1 (M.op X1 X1)))))) = (M.op (M.op X1 (M.op X2 (M.op X1 (M.op X1 X1)))) (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60869 X0 X0 X2
       have i₂ := eq1264 X0 X0
       grind)
    | exact superpose eq1264 eq60869
    | exact resolve eq60869 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60869
  have eq60888 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X2 (M.op X1 X1)) (M.op X2 X1))) = (M.op (M.op X2 X1) (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60882 X0 X0 X2
       have i₂ := eq3829 X0 X0 X2
       grind)
    | exact superpose eq3829 eq60882
    | exact resolve eq60882 eq3829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3829 eq60882
  have eq60891 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X1 X1))) = (M.op (M.op X2 X1) (M.op X0 (M.op X2 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq60888 X0 X1 X2
       have i₂ := eq8889 X1 X2
       grind)
    | exact superpose eq8889 eq60888
    | exact resolve eq60888 eq8889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8889 eq60888
  have eq78170 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq642 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642
  have eq78209 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq78170 (σ X0)
       have i₂ := eq31 X0 (σ X0)
       grind)
    | exact superpose eq31 eq78170
    | (have j0 := eq78170 (σ X0)
       grind)
    | exact resolve eq78170 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq78170
  have eq78210 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq78209 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq78209
    | (have j0 := eq78209 X0
       grind)
    | exact resolve eq78209 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78209
  have eq78213 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq78210 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq78210
    | (have j0 := eq78210 X0
       grind)
    | exact resolve eq78210 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78210
  have eq78218 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq78213 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq78213
    | (have j0 := eq78213 (σ X0)
       grind)
    | exact resolve eq78213 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78213
  have eq160799 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op (σ (M.op (τ X0) (τ X0))) X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq38700 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq38700
    | exact resolve eq38700 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175662 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X2 (M.op X3 X0))) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) (M.op X3 (M.op X0 X0))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1083 X0 X1 X2 X3
       have i₂ := eq60891 (M.op X0 (M.op (M.op X1 X0) X0)) X0 X3
       grind)
    | exact superpose eq60891 eq1083
    | exact resolve eq1083 eq60891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1083 eq60891
  have eq175663 : ∀ X0 X2 X3 : G, (M.op X2 (M.op X2 (M.op X3 X0))) = (M.op (M.op X0 (M.op X0 X0)) (M.op X3 (M.op X0 X0))) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq175662 X0 x X2 X3
       have i₂ := eq1264 X0 x
       grind)
    | exact superpose eq1264 eq175662
    | exact resolve eq175662 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175662
  have eq296496 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq38839 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38839
  have eq296596 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq296496 x y
       grind)
    | exact superpose eq296496 eq16
    | (have j1 := eq296496 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq296496 x y
       grind)
    | exact resolve eq16 eq296496
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296496
  have eq296858 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq296596
  have eq296897 : y = (k y (τ (σ x))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq67 y
       have i₂ := eq296858
       grind)
    | exact superpose eq296858 eq67
    | exact resolve eq67 eq296858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297177 : y = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq296897
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq296897
    | exact resolve eq296897 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296897
  have eq297193 : y = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq38809 y x
       have i₂ := eq297177
       grind)
    | exact superpose eq297177 eq38809
    | (have j0 := eq38809 y x
       grind)
    | exact resolve eq38809 eq297177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297177
  have eq297195 : y = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq297193
  have eq297225 : (M.op x y) = (k (M.op x y) y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1880 y x
       have i₂ := eq297195
       grind)
    | exact superpose eq297195 eq1880
    | exact resolve eq1880 eq297195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1880
  have eq297419 : y = (k y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq297195 eq297225
    | exact resolve eq297225 eq297195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297195 eq297225
  have eq297482 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq37834 y y
       have i₂ := eq297419
       grind)
    | exact superpose eq297419 eq37834
    | (have j0 := eq37834 y y
       grind)
    | exact resolve eq37834 eq297419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37834 eq297419
  have eq297483 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq297482
  have eq297489 : x = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq296858 eq297483
    | exact resolve eq297483 eq296858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297483
  have eq297908 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq297489 eq296858
    | exact resolve eq296858 eq297489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296858
  have eq297912 : ∀ X0 : G, y = (M.op X0 (M.op X0 x)) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq1134 y X0
       have i₂ := eq297489
       grind)
    | exact superpose eq297489 eq1134
    | exact resolve eq1134 eq297489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297489
  have eq299465 : ∀ X0 : G, (M.op (σ (M.op (τ X0) (τ X0))) X0) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq160799 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160799
  have eq301241 : ∀ X0 X1 : G, (M.op (σ (M.op (τ X0) (τ X0))) X0) = (M.op X1 (M.op X1 X0)) ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1087 X1 X0 (σ (M.op (τ X0) (τ X0)))
       have i₂ := eq299465 X0
       grind)
    | exact superpose eq299465 eq1087
    | (have j1 := eq299465 X0
       grind)
    | exact resolve eq1087 eq299465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq301242 : ∀ X0 : G, (M.op X0 (M.op (σ (M.op (τ X0) (τ X0))) X0)) = X0 ∨ (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1099 (σ (M.op (τ X0) (τ X0))) X0
       have i₂ := eq299465 X0
       grind)
    | exact superpose eq299465 eq1099
    | (have j1 := eq299465 X0
       grind)
    | exact resolve eq1099 eq299465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1099
  have eq301586 : ∀ X0 : G, (τ (M.op (σ (M.op (τ (σ X0)) (τ (σ X0)))) (σ X0))) = (k (τ (M.op (σ (M.op (τ (σ X0)) (τ (σ X0)))) (σ X0))) X0) ∨ (σ (M.op (τ (σ X0)) (τ (σ X0)))) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3077 (σ (M.op (τ (σ x)) (τ (σ x)))) x
       have i₂ := eq299465 (σ x)
       grind)
    | exact superpose eq299465 eq3077
    | (have j1 := eq299465 (σ X0)
       grind)
    | exact resolve eq3077 eq299465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3077
  have eq301625 : ∀ X0 : G, (τ (M.op (σ (M.op X0 X0)) (σ X0))) = (k (τ (M.op (σ (M.op X0 X0)) (σ X0))) X0) ∨ (σ (M.op (τ (σ X0)) (τ (σ X0)))) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq301586 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq301586
    | (have j0 := eq301586 X0
       grind)
    | exact resolve eq301586 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301586
  have eq301886 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq299465 eq301242
    | (have j0 := eq301242 X0
       have j1 := eq299465 X0
       grind)
    | exact resolve eq301242 eq299465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301242
  have eq301887 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X1 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq299465 eq301241
    | (have j0 := eq301241 X0 X1
       have j1 := eq299465 X0
       grind)
    | exact resolve eq301241 eq299465
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq299465 eq301241
  have eq301926 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (τ (M.op (σ (M.op X0 X0)) (σ X0))) = (k (τ (M.op (σ (M.op X0 X0)) (σ X0))) X0) := by
    intro X0
    first
    | (have i₁ := eq301625 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq301625
    | (have j0 := eq301625 X0
       grind)
    | exact resolve eq301625 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301625
  have eq302129 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (τ (σ X0)) = (k (τ (σ X0)) X0) := by
    intro X0
    first
    | exact superpose eq38700 eq301926
    | (have j0 := eq301926 X0
       have j1 := eq38700 X0
       grind)
    | exact resolve eq301926 eq38700
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38700 eq301926
  have eq302244 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq302129 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq302129
    | (have j0 := eq302129 X0
       grind)
    | exact resolve eq302129 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302129
  have eq302364 : x = (k x (τ (σ x))) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq67 x
       have i₂ := eq297908
       grind)
    | exact superpose eq297908 eq67
    | exact resolve eq67 eq297908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq297908
  have eq302718 : x = (k x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq302364
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq302364
    | exact resolve eq302364 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302364
  have eq302817 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq38809 x x
       have i₂ := eq302718
       grind)
    | exact superpose eq302718 eq38809
    | (have j0 := eq38809 x x
       grind)
    | exact resolve eq38809 eq302718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38809 eq302718
  have eq302820 : x = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq302817
  have eq302880 : x ≠ x ∨ x = y ∨ x = (k y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq302820
       grind)
    | exact superpose eq302820 eq13
    | (have j0 := eq13 x x
       grind)
    | exact resolve eq13 eq302820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq302891 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1264 y y
       have i₂ := eq302820
       grind)
    | exact superpose eq302820 eq1264
    | exact resolve eq1264 eq302820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq303039 : x = (k y y) ∨ x = y ∨ x = (M.op x x) := by grind
  clear eq302880
  have eq341278 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq301886 X0
       grind)
    | exact superpose eq301886 eq10
    | (have j1 := eq301886 X0
       grind)
    | exact resolve eq10 eq301886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301886
  have eq341513 : ∀ X0 X1 : G, (τ X0) = (M.op X1 (M.op X1 (τ (M.op X0 X0)))) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1134 (τ X0) X1
       have i₂ := eq341278 X0
       grind)
    | exact superpose eq341278 eq1134
    | (have j1 := eq341278 X0
       grind)
    | exact resolve eq1134 eq341278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq341278
  have eq342145 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) ∨ (k X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1264 (σ X0) (σ X0)
       have i₂ := eq302244 X0
       grind)
    | exact superpose eq302244 eq1264
    | (have j1 := eq302244 X0
       grind)
    | exact resolve eq1264 eq302244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264 eq302244
  have eq342749 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 (M.op X1 (k X0 (τ (σ X0))))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq341513 (σ X0) X1
       have i₂ := eq38870 (σ X0) X0
       grind)
    | exact superpose eq38870 eq341513
    | (have j0 := eq341513 (σ X0) X1
       have j1 := eq38870 (σ X0) X0
       grind)
    | exact resolve eq341513 eq38870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38870 eq341513
  have eq343168 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 (M.op X1 (k X0 (τ (σ X0))))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq342749 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342749
  have eq343368 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (k X0 X0))) = X0 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq343168 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq343168
    | (have j0 := eq343168 X0 X1
       grind)
    | exact resolve eq343168 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343168
  have eq394422 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) ∨ (M.op X1 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq301887 X0 X1
       grind)
    | exact superpose eq301887 eq10
    | (have j1 := eq301887 X0 X1
       grind)
    | exact resolve eq10 eq301887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq301887
  have eq400129 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (M.op X1 (M.op (k X0 X0) (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq175663 (k X0 X0) x (k X0 X0)
       have i₂ := eq343368 X0 (k X0 X0)
       grind)
    | exact superpose eq343368 eq175663
    | (have j1 := eq343368 X0 X1
       grind)
    | exact resolve eq175663 eq343368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175663 eq343368
  have eq400460 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq400129 X0 x
       have i₂ := eq1134 (k X0 X0) x
       grind)
    | exact superpose eq1134 eq400129
    | (have j0 := eq400129 X0 x
       grind)
    | exact resolve eq400129 eq1134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400129
  have eq400640 : ∀ X0 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq400460 eq78218
    | (have j0 := eq78218 X0
       have j1 := eq400460 X0
       grind)
    | exact resolve eq78218 eq400460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78218
  have eq400680 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ X0))) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1134 (σ X0) X1
       have i₂ := eq400460 X0
       grind)
    | exact superpose eq400460 eq1134
    | (have j1 := eq400460 X0
       grind)
    | exact resolve eq1134 eq400460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400460
  have eq403630 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 ∨ (M.op (τ X0) (τ X0)) = (k (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq400680 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq400680
    | (have j0 := eq400680 (τ X0) X1
       grind)
    | exact resolve eq400680 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400680
  have eq404351 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (M.op X1 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq403630 X0 X1
       have i₂ := eq34 X0 X0
       grind)
    | exact superpose eq34 eq403630
    | (have j0 := eq403630 X0 X1
       grind)
    | exact resolve eq403630 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq403630
  have eq404521 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (τ (k X0 X0)) ∨ (M.op X1 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq394422 eq404351
    | (have j0 := eq404351 X0 X1
       have j1 := eq394422 X0 X1
       grind)
    | exact resolve eq404351 eq394422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq394422 eq404351
  have eq404641 : ∀ X0 X1 : G, (k X0 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X1 (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X0 X0)
       have i₂ := eq404521 X0 X1
       grind)
    | exact superpose eq404521 eq11
    | (have j1 := eq404521 X0 X1
       grind)
    | exact resolve eq11 eq404521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404521
  have eq404706 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq404641 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq404641
    | (have j0 := eq404641 X0 X1
       grind)
    | exact resolve eq404641 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404641
  have eq405005 : y = (M.op y x) ∨ x = (k y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq404706 y y
       have i₂ := eq302820
       grind)
    | exact superpose eq302820 eq404706
    | exact resolve eq404706 eq302820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq404706
  have eq406479 : x = (M.op x x) ∨ x = (k y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq303039 eq405005
    | exact resolve eq405005 eq303039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq303039 eq405005
  have eq406480 : x = (k y y) ∨ x = (M.op x x) := by grind
  clear eq406479
  have eq417445 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (k y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq342145 y
       have i₂ := eq302820
       grind)
    | exact superpose eq302820 eq342145
    | (have j0 := eq342145 y
       grind)
    | exact resolve eq342145 eq302820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342145
  have eq417774 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq406480 eq417445
    | exact resolve eq417445 eq406480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406480 eq417445
  have eq417925 : (σ (M.op x y)) ≠ (σ x) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq417774
       grind)
    | exact superpose eq417774 eq16
    | exact resolve eq16 eq417774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq417774
  have eq418171 : (σ x) ≠ (σ x) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq302891 eq417925
    | exact resolve eq417925 eq302891
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302891 eq417925
  have eq418172 : x = (M.op x x) ∨ x = y := by grind
  clear eq418171
  have eq418227 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq418172 eq302820
    | exact resolve eq302820 eq418172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq302820 eq418172
  have eq418505 : x = (M.op x x) := by grind
  clear eq418227
  have eq418784 : ∀ X0 : G, x = (M.op X0 (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq1134 x X0
       have i₂ := eq418505
       grind)
    | exact superpose eq418505 eq1134
    | exact resolve eq1134 eq418505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1134
  have eq418841 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq400640 x
       have i₂ := eq418505
       grind)
    | exact superpose eq418505 eq400640
    | (have j0 := eq400640 x
       grind)
    | exact resolve eq400640 eq418505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400640
  have eq419001 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq418841
  have eq419240 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq297912 x
       have i₂ := eq418784 x
       grind)
    | exact superpose eq418784 eq297912
    | exact resolve eq297912 eq418784
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297912 eq418784
  have eq421151 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq419240
       grind)
    | exact superpose eq419240 eq10
    | exact resolve eq10 eq419240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419240
  have eq421333 : x = y ∨ x = y := by
    first
    | (have i₁ := eq421151
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq421151
    | exact resolve eq421151 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421151
  have eq421334 : x = y := by grind
  clear eq421333
  have eq421360 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq421334
       grind)
    | exact superpose eq421334 eq16
    | exact resolve eq16 eq421334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421334
  have eq421380 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq421360
       have i₂ := eq418505
       grind)
    | exact superpose eq418505 eq421360
    | exact resolve eq421360 eq418505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418505 eq421360
  have eq421381 : False := by grind
  exact eq421381

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,X) else if m(X,X) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pxx_y_pxx_x_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
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
  clear eq44
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq14 X0 X2 X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq64 (σ X0)
       grind)
    | exact superpose eq64 eq10
    | exact resolve eq10 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq64 sF2
       grind)
    | exact superpose eq64 eq50
    | exact resolve eq50 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq69 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq68
       have i₂ := eq64 x
       grind)
    | exact superpose eq64 eq68
    | exact resolve eq68 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq71 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq66 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq66
    | exact resolve eq66 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq103 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq104 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq108 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq64 sF3
       grind)
    | exact superpose eq64 eq104
    | exact resolve eq104 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq110 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq64 y
       grind)
    | exact superpose eq64 eq108
    | exact resolve eq108 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq103
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq103
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq103 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq118 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq112
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq112
    | exact resolve eq112 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq21 eq118
    | exact resolve eq118 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq119
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq119
    | exact resolve eq119 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq148 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq16
    | exact resolve eq16 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq261 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 X0 (τ X0)
       have i₂ := eq64 (τ X0)
       grind)
    | exact superpose eq64 eq35
    | exact resolve eq35 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq272 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq261 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq261
    | exact resolve eq261 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq274 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq272 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq272
    | exact resolve eq272 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq272
  have eq408 : ∀ X0 X1 X2 : G, (M.op (M.op X1 (M.op (M.op X2 X0) X0)) (M.op (M.op X2 X0) X0)) = (M.op X0 (M.op (M.op X2 X0) X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq14 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq696 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq274 X0
       grind)
    | exact superpose eq274 eq16
    | exact resolve eq16 eq274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq894 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X0 X2 X0 X1
       have i₂ := eq14 X0 X0 X1
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1227 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq894 X1 x X3
       have i₂ := eq894 X1 x X0
       grind)
    | exact superpose eq894 eq894
    | exact resolve eq894 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1243 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 x
       have i₂ := eq894 X1 x X0
       grind)
    | exact superpose eq894 eq14
    | exact resolve eq14 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1255 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X0 (M.op X2 X0) X2
       have i₂ := eq894 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq894 eq54
    | exact resolve eq54 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894
  have eq1262 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1255 X0 X1 X2
       have i₂ := eq54 X0 X0 X1
       grind)
    | exact superpose eq54 eq1255
    | exact resolve eq1255 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1255
  have eq1282 : y = (M.op y (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq1243 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1243
    | (have j0 := eq1243 x y
       grind)
    | exact resolve eq1243 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1283 : (σ y) = (M.op (σ y) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq1243
    | (have j0 := eq1243 (σ x) (σ y)
       grind)
    | exact resolve eq1243 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1290 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq1243 X0 (M.op X0 X0)
       have i₂ := eq1243 X0 X0
       grind)
    | exact superpose eq1243 eq1243
    | exact resolve eq1243 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1489 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1290 (σ X0)
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq1290
    | exact resolve eq1290 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq1490 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1290 (τ X0)
       have i₂ := eq696 X0
       grind)
    | exact superpose eq696 eq1290
    | exact resolve eq1290 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1496 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1 X0
       have i₂ := eq1290 X0
       grind)
    | exact superpose eq1290 eq54
    | exact resolve eq54 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1497 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X0 X1 X0
       have i₂ := eq1290 X0
       grind)
    | exact superpose eq1290 eq14
    | exact resolve eq14 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2057 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1227 X0 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq1243 X1 X0
       grind)
    | exact superpose eq1243 eq1227
    | exact resolve eq1227 eq1243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2077 : ∀ X0 : G, (M.op y y) = (M.op X0 (M.op X0 (M.op x (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq1282 eq1227
    | exact resolve eq1227 eq1282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282
  have eq2081 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (M.op X0 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | exact superpose eq1283 eq1227
    | exact resolve eq1227 eq1283
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1283
  have eq2282 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq1262 X0 X1 X0
       have i₂ := eq1290 X0
       grind)
    | exact superpose eq1290 eq1262
    | exact resolve eq1262 eq1290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262 eq1290
  have eq4264 : ∀ X0 : G, (M.op y y) = (M.op x (M.op X0 (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have i₁ := eq2077 x
       have i₂ := eq1227 x sF0 x
       grind)
    | (have i₁ := eq2077 x
       have i₂ := eq1227 X0 sF0 x
       grind)
    | exact superpose eq1227 eq2077
    | exact resolve eq2077 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4390 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X1 (M.op X0 X0)) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq408 X0 X1 X1
       have i₂ := eq2282 X0 X1
       grind)
    | exact superpose eq2282 eq408
    | exact resolve eq408 eq2282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq4391 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4390 X0 x
       have i₂ := eq2282 (M.op X0 X0) x
       grind)
    | exact superpose eq2282 eq4390
    | exact resolve eq4390 eq2282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4390
  have eq15535 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (M.op (τ (M.op X0 X0)) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1243 (τ (M.op X0 X0)) (τ X0)
       have i₂ := eq1490 X0
       grind)
    | exact superpose eq1490 eq1243
    | exact resolve eq1243 eq1490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1490
  have eq15549 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op (M.op X0 X0) (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq15535 X0
       have i₂ := eq696 (M.op X0 X0)
       grind)
    | exact superpose eq696 eq15535
    | exact resolve eq15535 eq696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696 eq15535
  have eq15584 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ (M.op X0 (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq15549 X0
       have i₂ := eq4391 X0
       grind)
    | exact superpose eq4391 eq15549
    | exact resolve eq15549 eq4391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4391 eq15549
  have eq16352 : (M.op x y) = (M.op (M.op x y) (τ (M.op (σ (M.op x y)) (M.op (σ (M.op x y)) (σ (M.op x y)))))) := by
    first
    | exact superpose eq31 eq15584
    | exact resolve eq15584 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq15584
  have eq16481 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) (τ (M.op X0 (M.op X0 (σ (M.op x y)))))) := by
    intro X0
    first
    | (have i₁ := eq16352
       have i₂ := eq1227 sF1 sF1 x
       grind)
    | (have i₁ := eq16352
       have i₂ := eq1227 X0 sF1 sF1
       grind)
    | exact superpose eq1227 eq16352
    | exact resolve eq16352 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227 eq16352
  have eq16560 : ∀ X0 X1 : G, (τ (M.op X1 (M.op X1 (σ (M.op x y))))) = (M.op X0 (M.op X0 (M.op (M.op x y) (τ (M.op X1 (M.op X1 (σ (M.op x y)))))))) := by
    intro X0 X1
    first
    | exact superpose eq16481 eq14
    | exact resolve eq14 eq16481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16583 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op x y))) = (τ (M.op X1 (M.op X1 (σ (M.op x y))))) := by
    intro X0 X1
    first
    | exact superpose eq16481 eq16560
    | exact resolve eq16560 eq16481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16560
  have eq22506 : ∀ X0 : G, (M.op y y) = (M.op x (τ (M.op X0 (M.op X0 (σ (M.op x y)))))) := by
    intro X0
    first
    | exact superpose eq16583 eq4264
    | exact resolve eq4264 eq16583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4264 eq16583
  have eq27108 : (M.op (M.op x y) (M.op x y)) = (M.op x (M.op y y)) := by
    first
    | exact superpose eq2077 eq2057
    | exact resolve eq2057 eq2077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2077
  have eq27111 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ x) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq2081 eq2057
    | exact resolve eq2057 eq2081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2057 eq2081
  have eq27646 : y = (M.op x (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1497 y x
       have i₂ := eq27108
       grind)
    | exact superpose eq27108 eq1497
    | exact resolve eq1497 eq27108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27108
  have eq27686 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq27646 eq1496
    | exact resolve eq1496 eq27646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27752 : y = (M.op x (M.op y (M.op x y))) := by
    first
    | exact superpose eq27686 eq27646
    | exact resolve eq27646 eq27686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27646 eq27686
  have eq27959 : (σ y) = (M.op (σ x) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27111 eq1497
    | exact resolve eq1497 eq27111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1497 eq27111
  have eq27999 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27959 eq1496
    | exact resolve eq1496 eq27959
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1496
  have eq28050 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27999 eq27959
    | exact resolve eq27959 eq27999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27959 eq27999
  have eq32244 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq120 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq32245 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq32244
    | exact resolve eq32244 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32244
  have eq32256 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq32245
       have r₂ := eq28
       grind)
    | exact resolve eq32245 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32245
  have eq32260 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq32256
    | exact resolve eq32256 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32256
  have eq32280 : (σ x) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq32260 eq1243
    | exact resolve eq1243 eq32260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32260
  have eq32295 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28050 eq32280
    | exact resolve eq32280 eq28050
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28050 eq32280
  have eq32300 : (τ (σ x)) = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq32295 eq148
    | exact resolve eq148 eq32295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148 eq32295
  have eq32408 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq29 eq32300
    | exact resolve eq32300 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32300
  have eq32409 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by grind
  clear eq32408
  have eq32440 : x = (M.op x (M.op y (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1243 y x
       have i₂ := eq32409
       grind)
    | exact superpose eq32409 eq1243
    | exact resolve eq1243 eq32409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1243 eq32409
  have eq32455 : x = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27752 eq32440
    | exact resolve eq32440 eq27752
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27752 eq32440
  have eq32803 : x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2282 y y
       have i₂ := eq32455
       grind)
    | exact superpose eq32455 eq2282
    | exact resolve eq2282 eq32455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2282 eq32455
  have eq32813 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq32803
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq32803
    | exact resolve eq32803 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32803
  have eq32856 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq32813 eq30
    | exact resolve eq30 eq32813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq32813
  have eq33029 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq32856
    | exact resolve eq32856 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq32856
  have eq33030 : x = (M.op x y) ∨ x = y := by grind
  clear eq33029
  have eq33057 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq33030 eq21
    | exact resolve eq21 eq33030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33154 : ∀ X0 : G, x = (M.op x (τ (M.op X0 (M.op X0 (σ (M.op x y)))))) ∨ x = y := by
    intro X0
    first
    | exact superpose eq33030 eq16481
    | exact resolve eq16481 eq33030
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16481 eq33030
  have eq33176 : x = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq22506 eq33154
    | exact resolve eq33154 eq22506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22506 eq33154
  have eq33253 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq33057
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq33057
    | exact resolve eq33057 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33057
  have eq33821 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq1489 y
       have i₂ := eq33176
       grind)
    | exact superpose eq33176 eq1489
    | exact resolve eq1489 eq33176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1489 eq33176
  have eq33885 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq33821
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq33821
    | exact resolve eq33821 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33821
  have eq33904 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq33885
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq33885
    | exact resolve eq33885 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33885
  have eq33910 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq27 eq33904
    | exact resolve eq33904 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33904
  have eq33911 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq33910 eq28
    | exact resolve eq28 eq33910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33910
  have eq33967 : x = y := by
    first
    | (have r₁ := eq33911
       have r₂ := eq33253
       grind)
    | exact resolve eq33911 eq33253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33253 eq33911
  have eq33972 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq33967
       grind)
    | exact superpose eq33967 eq19
    | exact resolve eq19 eq33967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq33973 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq33967
       grind)
    | exact superpose eq33967 eq25
    | exact resolve eq25 eq33967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq33967
  have eq34151 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq33973
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq33973
    | exact resolve eq33973 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq33973
  have eq34181 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq34151 eq27
    | exact resolve eq27 eq34151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq34151
  have eq34593 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq34181 eq69
    | exact resolve eq69 eq34181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq34181
  have eq34699 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq34593
       have i₂ := eq33972
       grind)
    | exact superpose eq33972 eq34593
    | exact resolve eq34593 eq33972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33972 eq34593
  have eq34726 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34699 eq15
    | exact resolve eq15 eq34699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34699
  have eq34816 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq34726
    | exact resolve eq34726 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq34726
  have eq34846 : False := by grind
  exact eq34846

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyx_pxy_x_pyx_Equation723 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X0) X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  clear eq22
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X3 X0) X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op (M.op X3 X0) X0))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op (M.op X3 X0) X0)) X1 X2
       have i₂ := eq9 X0 X2 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq62 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 (M.op (M.op X2 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X2 X0) X0) (M.op X1 (M.op (M.op X2 X0) X0)) X1
       have i₂ := eq9 X0 (M.op X1 (M.op (M.op X2 X0) X0)) X2
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
  have eq71 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq64 (τ X0)
       grind)
    | exact superpose eq64 eq18
    | exact resolve eq18 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq74 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
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
  clear eq67
  have eq82 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq74
    | exact resolve eq74 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq74
  have eq101 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq82 X0
       grind)
    | exact superpose eq82 eq10
    | exact resolve eq10 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq2789 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq2864 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2789 X0 X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq2789
    | (have j0 := eq2789 X0 X1
       grind)
    | exact resolve eq2789 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2789
  have eq2915 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) X0)) = (M.op X2 (M.op X2 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X0 X2 X0 X1
       have i₂ := eq9 X0 X0 X1
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2941 : ∀ X0 X1 X3 : G, (M.op X0 (M.op X0 X1)) = (M.op X3 (M.op X3 X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq2915 X1 x X3
       have i₂ := eq2915 X1 x X0
       grind)
    | exact superpose eq2915 eq2915
    | exact resolve eq2915 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2956 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 x
       have i₂ := eq2915 X1 x X0
       grind)
    | exact superpose eq2915 eq9
    | exact resolve eq9 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2972 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X0 (M.op (M.op X1 X0) X0)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq62 X0 (M.op X2 X0) X2
       have i₂ := eq2915 X0 X1 (M.op X2 X0)
       grind)
    | exact superpose eq2915 eq62
    | exact resolve eq62 eq2915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2915
  have eq2990 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2972 X0 X1 X2
       have i₂ := eq62 X0 X0 X1
       grind)
    | exact superpose eq62 eq2972
    | exact resolve eq2972 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2972
  have eq3016 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq2956 X0 (M.op X0 X0)
       have i₂ := eq2956 X0 X0
       grind)
    | exact superpose eq2956 eq2956
    | exact resolve eq2956 eq2956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3037 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq3016 X0
       grind)
    | exact superpose eq3016 eq9
    | exact resolve eq9 eq3016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3058 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq3037 (σ X0) X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq3037
    | exact resolve eq3037 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3087 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2941 X1 (M.op X1 (M.op X0 X0)) X2
       have i₂ := eq3037 X0 X1
       grind)
    | exact superpose eq3037 eq2941
    | exact resolve eq2941 eq3037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3037
  have eq3095 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X1 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2941 X0 (M.op X1 (M.op X1 X0)) X2
       have i₂ := eq2956 X1 X0
       grind)
    | exact superpose eq2956 eq2941
    | exact resolve eq2941 eq2956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3248 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2990 X0 X1 X0
       have i₂ := eq3016 X0
       grind)
    | exact superpose eq3016 eq2990
    | exact resolve eq2990 eq3016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2990 eq3016
  have eq3336 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X0 X0)) = (M.op X1 (M.op X1 (M.op X0 (M.op X2 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq61 X0 X1 X2 X1
       have i₂ := eq3248 X0 X1
       grind)
    | exact superpose eq3248 eq61
    | exact resolve eq61 eq3248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq3337 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X0 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X0 X1 X1
       have i₂ := eq3248 X0 X1
       grind)
    | exact superpose eq3248 eq62
    | exact resolve eq62 eq3248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq3248
  have eq3378 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op (M.op X0 (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3337 X1 X1
       have i₂ := eq2941 X1 X1 X0
       grind)
    | (have i₁ := eq3337 X1 X1
       have i₂ := eq2941 X0 X1 X1
       grind)
    | exact superpose eq2941 eq3337
    | exact resolve eq3337 eq2941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3337
  have eq3513 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2956 (M.op X1 (M.op X1 X0)) X0
       have i₂ := eq3378 X1 X0
       grind)
    | exact superpose eq3378 eq2956
    | exact resolve eq2956 eq3378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3378
  have eq3573 : ∀ X0 X1 : G, (σ (σ X0)) = (M.op X1 (M.op X1 (σ (σ (M.op X0 X0))))) := by
    intro X0 X1
    first
    | (have i₁ := eq3058 (σ X0) X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq3058
    | exact resolve eq3058 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3058
  have eq3923 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op (M.op X1 X0) (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3095 (M.op X1 X0) X1 X1
       have i₂ := eq3095 X0 X1 X1
       grind)
    | exact superpose eq3095 eq3095
    | exact resolve eq3095 eq3095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3928 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3095 X2 X1 X1
       have i₂ := eq2941 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq3095 X2 X1 X1
       have i₂ := eq2941 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq2941 eq3095
    | exact resolve eq3095 eq2941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2941 eq3095
  have eq5178 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op X1 (M.op X2 (M.op X2 (M.op X1 (σ X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3928 X2 X1 (σ X0)
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq3928
    | exact resolve eq3928 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5194 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0)) (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3928 X2 X0 (M.op (M.op X1 (M.op X1 X0)) (M.op X0 X0))
       have i₂ := eq3513 X0 X1
       grind)
    | exact superpose eq3513 eq3928
    | exact resolve eq3928 eq3513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3513
  have eq5381 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op X1 (M.op X1 X0)) (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5194 X0 X1 X2
       have i₂ := eq3923 (M.op X0 X0) (M.op X1 (M.op X1 X0))
       grind)
    | exact superpose eq3923 eq5194
    | exact resolve eq5194 eq3923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5194
  have eq5429 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X2 (M.op X2 X0))) = (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5381 X0 X1 X2
       have i₂ := eq3923 X0 X0
       grind)
    | exact superpose eq3923 eq5381
    | exact resolve eq5381 eq3923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5381
  have eq5467 : ∀ X0 X1 : G, (M.op (M.op X1 (M.op X1 X0)) (M.op X0 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq5429 X0 X1 x
       have i₂ := eq2956 x X0
       grind)
    | exact superpose eq2956 eq5429
    | exact resolve eq5429 eq2956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2956 eq5429
  have eq6173 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) = (M.op (M.op X1 (M.op X0 (M.op X1 X1))) (M.op X1 (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3087 (M.op X1 (M.op X0 (M.op X1 X1))) (M.op X1 (M.op X0 (M.op X1 X1))) X2
       have i₂ := eq3336 X1 (M.op X1 (M.op X0 (M.op X1 X1))) X0
       grind)
    | exact superpose eq3336 eq3087
    | exact resolve eq3087 eq3336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3336
  have eq6289 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) = (M.op X1 (M.op (M.op X0 (M.op X1 X1)) (M.op X0 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6173 X0 X1 X2
       have i₂ := eq3923 (M.op X0 (M.op X1 X1)) X1
       grind)
    | exact superpose eq3923 eq6173
    | exact resolve eq6173 eq3923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6173
  have eq6322 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) = (M.op X1 (M.op X0 (M.op (M.op X1 X1) (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6289 X0 X1 X2
       have i₂ := eq3923 (M.op X1 X1) X0
       grind)
    | exact superpose eq3923 eq6289
    | exact resolve eq6289 eq3923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6289
  have eq6337 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 (M.op X1 X1)))) = (M.op X1 (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq6322 X0 X1 X2
       have i₂ := eq3923 X1 X1
       grind)
    | exact superpose eq3923 eq6322
    | exact resolve eq6322 eq3923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6322
  have eq6343 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 (M.op X0 (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq6337 X0 X1 x
       have i₂ := eq3087 X1 X0 x
       grind)
    | exact superpose eq3087 eq6337
    | exact resolve eq6337 eq3087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3087 eq6337
  have eq10301 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 (M.op X1 X1))) (M.op X0 (M.op X1 (M.op X1 X1)))) = (M.op X1 (M.op X2 (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3928 X2 X1 (M.op X0 (M.op X1 (M.op X1 X1)))
       have i₂ := eq6343 X0 X1
       grind)
    | exact superpose eq6343 eq3928
    | exact resolve eq3928 eq6343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3928 eq6343
  have eq10323 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X2 (M.op X2 (M.op X0 X1)))) = (M.op X0 (M.op (M.op X1 (M.op X1 X1)) (M.op X1 (M.op X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10301 X0 X1 X2
       have i₂ := eq3923 (M.op X1 (M.op X1 X1)) X0
       grind)
    | exact superpose eq3923 eq10301
    | exact resolve eq10301 eq3923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3923 eq10301
  have eq10364 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 (M.op X2 (M.op X2 (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10323 X0 X1 X2
       have i₂ := eq5467 X1 X1
       grind)
    | exact superpose eq5467 eq10323
    | exact resolve eq10323 eq5467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5467 eq10323
  have eq65822 : ∀ X0 X1 X2 : G, (σ (M.op X0 X0)) = (M.op (σ X1) (M.op X2 (M.op X2 (M.op (σ X0) (σ X1))))) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq5178 X0 (σ X1) X2
       have i₂ := eq2864 X0 X1
       grind)
    | (have i₁ := eq5178 X1 (σ X0) X2
       have i₂ := eq2864 X0 X1
       grind)
    | exact superpose eq2864 eq5178
    | (have j1 := eq2864 X0 X1
       grind)
    | exact resolve eq5178 eq2864
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2864 eq5178
  have eq66353 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq65822 X0 X1 x
       have i₂ := eq10364 (σ X0) (σ X1) x
       grind)
    | exact superpose eq10364 eq65822
    | (have j0 := eq65822 X0 X1 x
       grind)
    | exact resolve eq65822 eq10364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65822
  have eq66354 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq66353 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66353
  have eq67980 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq66354 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66354
  have eq69574 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq67980 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67980
  have eq73753 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq69574 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69574
  have eq75553 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq73753 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73753
  have eq77187 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq75553 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75553
  have eq78530 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq77187 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77187
  have eq79600 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq78530 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78530
  have eq80815 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq79600 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79600
  have eq80824 : ∀ X0 X1 : G, (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) ∨ (σ (M.op (σ X1) (σ X1))) = (M.op (σ (σ X1)) (σ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq80815 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq80815
    | (have j0 := eq80815 (σ X0) (σ X1)
       grind)
    | exact resolve eq80815 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80829 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq80815 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq80815
    | (have j0 := eq80815 (τ X0) (τ X1)
       grind)
    | exact resolve eq80815 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80815
  have eq80964 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq80829 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq80829
    | (have j0 := eq80829 X0 X1
       grind)
    | exact resolve eq80829 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80829
  have eq80965 : ∀ X0 X1 : G, (σ (σ (M.op X1 X1))) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (M.op (σ (σ X1)) (σ (σ X0))) = (σ (σ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq80824 X0 X1
       have i₂ := eq78 X1
       grind)
    | exact superpose eq78 eq80824
    | (have j0 := eq80824 X0 X1
       grind)
    | exact resolve eq80824 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq80824
  have eq80986 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq80964 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq80964
    | (have j0 := eq80964 X0 X1
       grind)
    | exact resolve eq80964 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80964
  have eq80997 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq80986 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq80986
    | (have j0 := eq80986 X0 X1
       grind)
    | exact resolve eq80986 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80986
  have eq81004 : ∀ X0 X1 : G, (σ (M.op (τ X1) (τ X1))) = (M.op (σ (τ X1)) X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq80997 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq80997
    | (have j0 := eq80997 X0 X1
       grind)
    | exact resolve eq80997 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80997
  have eq81009 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X1) (τ X1))) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81004 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq81004
    | (have j0 := eq81004 X0 X1
       grind)
    | exact resolve eq81004 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81004
  have eq81014 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (M.op X1 X1))) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81009 X0 X1
       have i₂ := eq101 X1
       grind)
    | exact superpose eq101 eq81009
    | (have j0 := eq81009 X0 X1
       grind)
    | exact resolve eq81009 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq81009
  have eq81017 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq81014 X0 X1
       have i₂ := eq11 (M.op X1 X1)
       grind)
    | exact superpose eq11 eq81014
    | (have j0 := eq81014 X0 X1
       grind)
    | exact resolve eq81014 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81014
  have eq240356 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq81017 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq81017 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq81017 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq81017 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81017
  have eq240537 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq240356 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240356
  have eq242203 : ∀ X0 X1 X2 : G, (σ (σ (M.op X0 X0))) = (M.op (σ (σ X1)) (M.op X2 (M.op X2 (σ (σ (M.op X0 X0)))))) ∨ (σ (σ (k X1 X0))) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10364 (σ (σ X1)) (σ (σ X0)) X2
       have i₂ := eq80965 X0 X1
       grind)
    | exact superpose eq80965 eq10364
    | (have j1 := eq80965 X1 X0
       grind)
    | exact resolve eq10364 eq80965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10364
  have eq242283 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ (M.op X0 X0))) = (k (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ (k X1 X0))) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq240537 (σ (σ X0)) (σ (σ X1))
       have i₂ := eq80965 X0 X1
       grind)
    | exact superpose eq80965 eq240537
    | (have j1 := eq80965 X1 X0
       grind)
    | exact resolve eq240537 eq80965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240537
  have eq242286 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) ≠ (σ (σ (k X1 X0))) ∨ (σ (σ (k X1 X0))) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq80965 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80965
  have eq242288 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (σ (k (σ X1) (σ X0))) ∨ (σ (σ (M.op X0 X0))) ≠ (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ (k X1 X0))) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq242283 X0 X1
       have i₂ := eq15 (σ X1) (σ X0)
       grind)
    | exact superpose eq15 eq242283
    | (have j0 := eq242283 X0 X1
       grind)
    | exact resolve eq242283 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242283
  have eq242339 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ (k X1 X0))) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq242203 X0 X1 x
       have i₂ := eq3573 X0 x
       grind)
    | exact superpose eq3573 eq242203
    | (have j0 := eq242203 X0 X1 x
       grind)
    | exact resolve eq242203 eq3573
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3573 eq242203
  have eq242694 : ∀ X0 X1 : G, (σ (σ (M.op X0 X0))) = (σ (σ (k X1 X0))) ∨ (σ (σ (M.op X0 X0))) ≠ (M.op (σ (σ X1)) (σ (σ X0))) ∨ (σ (σ (k X1 X0))) = (M.op (σ (σ X0)) (σ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq242288 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq242288
    | (have j0 := eq242288 X0 X1
       grind)
    | exact resolve eq242288 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242288
  have eq243009 : ∀ X0 X3 : G, (M.op (σ (σ X0)) (σ (σ X3))) = (σ (σ (k X3 X0))) := by
    intro X0 X3
    first
    | (have j0 := eq242694 X0 X3
       have j1 := eq242339 X0 X3
       have j2 := eq242286 X0 X3
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242286 eq242339 eq242694
  have eq252645 : ∀ X0 X1 : G, (σ (σ (k (τ X0) X1))) = (M.op (σ (σ X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq243009 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq243009
    | exact resolve eq243009 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243009
  have eq253327 : ∀ X0 X1 : G, (σ (k X0 (σ X1))) = (M.op (σ (σ X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq252645 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq252645
    | exact resolve eq252645 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq252645
  have eq268735 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq253327 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq253327
    | exact resolve eq253327 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253327
  have eq269051 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq268735 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq268735
    | exact resolve eq268735 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq268735
  have eq269189 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq269051 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq269051
    | exact resolve eq269051 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269051
  have eq269224 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (k X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq269189 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq269189
    | exact resolve eq269189 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269189
  have eq269247 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq269224 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq269224
    | exact resolve eq269224 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269224
  have eq269496 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq269247 X0 (τ X1)
       grind)
    | exact superpose eq269247 eq28
    | exact resolve eq28 eq269247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq269551 : ∀ X0 X1 : G, (M.op (τ X1) X0) = (τ (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq269496 X0 X1
       have i₂ := eq269247 (σ X0) X1
       grind)
    | exact superpose eq269247 eq269496
    | exact resolve eq269496 eq269247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269247 eq269496
  have eq269790 : ∀ X0 X1 : G, (M.op X0 (σ X1)) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (M.op X0 (σ X1))
       have i₂ := eq269551 X1 X0
       grind)
    | exact superpose eq269551 eq11
    | exact resolve eq11 eq269551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269551
  have eq271534 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq269790 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq269790
    | exact resolve eq269790 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq269790
  have eq272399 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq271534 x y
       grind)
    | exact superpose eq271534 eq16
    | (have r₁ := eq16
       have r₂ := eq271534 x y
       grind)
    | exact resolve eq16 eq271534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271534
  have eq272722 : False := by grind
  exact eq272722
