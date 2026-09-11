import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pxy_pxx_pxy_Equation1485 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
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
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq33 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq36 : ∀ X0 : G, (k (σ (M.op (τ X0) (τ X0))) X0) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  clear eq20
  have eq49 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  have eq50 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq49 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq63 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq86 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq33 X0 (σ X0)
       have i₂ := eq50 (σ X0)
       grind)
    | exact superpose eq50 eq33
    | exact resolve eq33 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq88 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq50 (τ X0)
       grind)
    | exact superpose eq50 eq19
    | exact resolve eq19 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq89 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq88 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq88
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq91 : ∀ X0 : G, (τ (M.op (σ X0) (σ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq86
    | exact resolve eq86 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq97 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq89 X0
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq89
    | exact resolve eq89 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq98 : ∀ X0 : G, (M.op X0 X0) = (τ (M.op (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq91 X0
       have i₂ := eq50 X0
       grind)
    | exact superpose eq50 eq91
    | exact resolve eq91 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq91
  have eq101 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq97 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq97
    | exact resolve eq97 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq109 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq10
    | exact resolve eq10 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq201 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq63 X0 X1
       have i₂ := eq101 X1
       grind)
    | exact superpose eq101 eq63
    | (have j0 := eq63 X0 X1
       grind)
    | exact resolve eq63 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq230 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq201 x y
       grind)
    | exact superpose eq201 eq16
    | (have j1 := eq201 x y
       grind)
    | exact resolve eq16 eq201
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq498 : ∀ X0 : G, (k (σ (τ (M.op X0 X0))) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq109 X0
       grind)
    | exact superpose eq109 eq36
    | exact resolve eq36 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq109
  have eq499 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq498 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq498
    | exact resolve eq498 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498
  have eq500 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (σ (M.op (τ (M.op X0 X0)) (τ X0))) := by
    intro X0
    grind
  clear eq499
  have eq543 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (τ (M.op (σ X0) (σ X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq500 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq500
    | exact resolve eq500 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq567 : ∀ X0 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq543 X0
       have i₂ := eq98 X0
       grind)
    | exact superpose eq98 eq543
    | exact resolve eq543 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq543
  have eq571 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq567 X0
       have i₂ := eq101 X0
       grind)
    | exact superpose eq101 eq567
    | exact resolve eq567 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq844 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq230
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq230
    | (have j1 := eq14 x y
       grind)
    | (have r₁ := eq230
       have r₂ := eq14 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq230
       have r₂ := eq14 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq230 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq845 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by grind
  clear eq844
  have eq11338 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq845
       grind)
    | exact superpose eq845 eq16
    | exact resolve eq16 eq845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq11339 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq11338
       have r₂ := eq101 x
       grind)
    | exact resolve eq11338 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11338
  have eq17707 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq11339
       grind)
    | exact superpose eq11339 eq10
    | exact resolve eq10 eq11339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11339
  have eq17788 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq17707
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq17707
    | exact resolve eq17707 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17707
  have eq18039 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17788
       grind)
    | exact superpose eq17788 eq16
    | exact resolve eq16 eq17788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17788
  have eq18040 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18039
       have r₂ := eq101 x
       grind)
    | exact resolve eq18039 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq18039
  have eq18356 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq18040
       grind)
    | exact superpose eq18040 eq10
    | exact resolve eq10 eq18040
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18040
  have eq18439 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq18356
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq18356
    | exact resolve eq18356 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18356
  have eq18440 : x = (M.op y y) := by grind
  clear eq18439
  have eq18466 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq571 y
       have i₂ := eq18440
       grind)
    | exact superpose eq18440 eq571
    | exact resolve eq571 eq18440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571 eq18440
  have eq18553 : False := by grind
  exact eq18553

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxy_pxx_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq37 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq37 (σ X0)
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq39 X0
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq39
    | exact resolve eq39 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq39
  have eq61 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq44 X1
       grind)
    | exact superpose eq44 eq61
    | (have j0 := eq61 X0 X1
       grind)
    | exact resolve eq61 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq90 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (M.op X1 (σ X0)) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq44 X0
       grind)
    | exact superpose eq44 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq66 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq66
    | exact resolve eq66 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq204 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq184 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq184
    | (have j0 := eq184 X0 X1
       grind)
    | exact resolve eq184 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq209 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq204 X0 X1
       have j1 := eq90 X1 X0
       grind)
    | (have r₁ := eq204 X1 X0
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq204 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq204 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq204
  have eq244 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq209 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq209
    | exact resolve eq209 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq209 (σ X0) X1
       grind)
    | exact superpose eq209 eq15
    | (have j1 := eq209 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq277 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq244 X1 (τ X0)
       grind)
    | exact superpose eq244 eq18
    | (have j1 := eq244 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq244
  have eq684 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq277 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq277
    | exact resolve eq277 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq277
  have eq718 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq684 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq684
    | (have j0 := eq684 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq684 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq1433 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq249 x y
       grind)
    | exact superpose eq249 eq16
    | (have j1 := eq249 x y
       grind)
    | exact resolve eq16 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq1467 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1433
       have i₂ := eq718 x y
       grind)
    | exact superpose eq718 eq1433
    | (have j1 := eq718 (σ x) (σ y)
       grind)
    | (have r₁ := eq1433
       have r₂ := eq718 x y
       grind)
    | (have r₁ := eq1433
       have r₂ := eq718 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1433
       have r₂ := eq718 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1433 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718 eq1433
  have eq1468 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1467
  have eq1472 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1468
       grind)
    | exact superpose eq1468 eq10
    | exact resolve eq10 eq1468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1468
  have eq1515 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1472
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1472
    | exact resolve eq1472 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1472
  have eq1516 : x = y := by grind
  clear eq1515
  have eq1586 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1516
       grind)
    | exact superpose eq1516 eq16
    | exact resolve eq16 eq1516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1516
  have eq1587 : False := by grind
  exact eq1587

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pxy_pyy_pxy_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq25 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq25 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq25 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq25 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
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
    | (have r₁ := eq13 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq38 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq38 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq44 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq46 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq46 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq59 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq52
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       have j1 := eq59 X0 X1
       grind)
    | (have r₁ := eq60 X0 X1
       have r₂ := eq59 X0 X1
       grind)
    | exact resolve eq60 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq60
  have eq108 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq56 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq112 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq108 X0 X1
       have j1 := eq63 X0 X1
       grind)
    | (have r₁ := eq108 X0 X1
       have r₂ := eq63 X0 X1
       grind)
    | (have r₁ := eq108 X0 X0
       have r₂ := eq63 X0 X0
       grind)
    | exact resolve eq108 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq108
  have eq389 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq112 (σ X0) (σ X1)
       grind)
    | exact superpose eq112 eq15
    | exact resolve eq15 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq389 X0 X1
       have i₂ := eq112 X0 X1
       grind)
    | exact superpose eq112 eq389
    | exact resolve eq389 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq389
  have eq396 : False := by grind
  exact eq396

/-- `Equation1486`: `x = (y ◇ x) ◇ (x ◇ (z ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pyx_pyx_pxx_pyx_Equation1486 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1486 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1486.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq87 : ∀ X0 X1 : G, (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq375 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq87 X1 X0
       grind)
    | (have i₁ := eq13 (σ X1) (σ X1)
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq87 X1 X0
       grind)
    | (have r₁ := eq13 (σ X0) (σ X0)
       have r₂ := eq87 X0 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq87 X0 X1
       grind)
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq378 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq375 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq379 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq378 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq381 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq379 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq379
    | (have j0 := eq379 X0 X1
       grind)
    | exact resolve eq379 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq379
  have eq385 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq381 X0 X1
       have j1 := eq377 X1 X0
       grind)
    | (have r₁ := eq381 X1 X0
       have r₂ := eq377 X0 X1
       grind)
    | (have r₁ := eq381 (k X1 X0) X1
       have r₂ := eq377 X0 X1
       grind)
    | (have r₁ := eq381 X1 X1
       have r₂ := eq377 X1 X1
       grind)
    | exact resolve eq381 eq377
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377 eq381
  have eq529 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq385 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq385
    | exact resolve eq385 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq541 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq385 y x
       grind)
    | exact superpose eq385 eq16
    | (have j1 := eq385 y x
       grind)
    | exact resolve eq16 eq385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq560 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq529 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq529
    | (have j0 := eq529 X0 X1
       grind)
    | exact resolve eq529 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq529
  have eq612 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq560 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq560
    | exact resolve eq560 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq695 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq612 (τ X1) X0
       grind)
    | exact superpose eq612 eq18
    | (have j1 := eq612 (τ X1) X0
       grind)
    | exact resolve eq18 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq612
  have eq883 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq695 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq695
    | exact resolve eq695 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq934 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq883 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq883
    | (have j0 := eq883 X0 X1
       grind)
    | exact resolve eq883 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883
  have eq1032 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq541
       have i₂ := eq934 y x
       grind)
    | exact superpose eq934 eq541
    | (have j1 := eq934 (σ y) (σ x)
       grind)
    | (have r₁ := eq541
       have r₂ := eq934 y x
       grind)
    | exact resolve eq541 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1033 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1032
  have eq1038 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1033
  have eq1095 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq541
       have i₂ := eq1038
       grind)
    | exact superpose eq1038 eq541
    | exact resolve eq541 eq1038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq541 eq1038
  have eq1096 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1095
  have eq1097 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1096
  have eq1110 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1097
  have eq1122 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1110
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1110
    | exact resolve eq1110 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1110
  have eq1195 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1122
       grind)
    | exact superpose eq1122 eq16
    | exact resolve eq16 eq1122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1122
  have eq1271 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1195
       have i₂ := eq934 y x
       grind)
    | exact superpose eq934 eq1195
    | (have j1 := eq934 y x
       grind)
    | (have r₁ := eq1195
       have r₂ := eq934 y x
       grind)
    | exact resolve eq1195 eq934
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq934
  have eq1272 : y = (M.op x x) := by grind
  clear eq1271
  have eq1278 : (M.op x y) = (k y x) := by grind
  clear eq1272
  have eq1342 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1195
       have i₂ := eq1278
       grind)
    | exact superpose eq1278 eq1195
    | exact resolve eq1195 eq1278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq1278
  have eq1345 : False := by grind
  exact eq1345

/-- `Equation1590`: `x = (y ◇ z) ◇ (z ◇ (y ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_x_pxx_pyx_pxy_Equation1590 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1590 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1590.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X2 (M.op X1 X0))) = X0 := by
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
  have eq44 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq45 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq44
  have eq48 : (σ (k x x)) = (k (σ x) (σ x)) := by
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
  have eq49 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, (M.op (M.op x y) (M.op y (M.op x X0))) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) X0))) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X2 (M.op X1 X0)) (M.op (M.op X1 X2) X3))) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X1 X2) (M.op X2 (M.op X1 X0))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op X0 (M.op x y))) := by
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
  have eq58 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X1 X0)) = (M.op (M.op (M.op X1 X2) X3) (M.op X3 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X2 (M.op X1 X0)) (M.op X1 X2) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (M.op (M.op X1 (M.op X2 X1)) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X2 X0) X1 (M.op X2 X1)
       have i₂ := eq14 X0 X2 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq16
    | exact resolve eq16 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq49
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq78 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq79 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq78
    | exact resolve eq78 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq80 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = y := by
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
  have eq89 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq100 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq96
  have eq101 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq100
  have eq122 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq125 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq122
  have eq126 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq125
  have eq165 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq126 eq16
    | exact resolve eq16 eq126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq215 : ∀ X0 : G, (M.op x X0) = (M.op (M.op y (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq223 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq27 eq54
    | (have j0 := eq54 (σ y)
       grind)
    | exact resolve eq54 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (M.op X1 (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ X0) (σ X0) X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq536 : ∀ X0 : G, y = (M.op X0 (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq56 eq59
    | exact resolve eq59 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 : G, (M.op y X0) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | exact superpose eq536 eq59
    | exact resolve eq59 eq536
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq640 : ∀ X0 : G, (M.op y (M.op x (M.op (M.op x y) X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq567 (M.op x (M.op sF0 X0))
       have i₂ := eq14 X0 sF0 x
       grind)
    | exact superpose eq14 eq567
    | exact resolve eq567 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567
  have eq738 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op (M.op X0 X3) (M.op X3 X2)) (M.op X0 X1))) = X1 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq55 X2 X3 (M.op X0 X3) X1
       have i₂ := eq59 X1 X3 X0
       grind)
    | exact superpose eq59 eq55
    | exact resolve eq55 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq59
  have eq1603 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq80 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1604 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1603
    | exact resolve eq1603 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603
  have eq1607 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq1604
       have r₂ := eq28
       grind)
    | exact resolve eq1604 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1604
  have eq1609 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq1607
    | exact resolve eq1607 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1607
  have eq1696 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1609 eq89
    | (have r₁ := eq89
       have r₂ := eq1609
       grind)
    | exact resolve eq89 eq1609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq1697 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1609 eq223
    | exact resolve eq223 eq1609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq1704 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1696
  have eq1705 : (k (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1704
  have eq1809 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1705 eq80
    | exact resolve eq80 eq1705
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq1705
  have eq1813 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1809
  have eq1911 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1813 eq1697
    | exact resolve eq1697 eq1813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1697
  have eq1930 : (σ y) = (M.op (σ x) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq1911
  have eq1935 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1930 eq54
    | exact resolve eq54 eq1930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq1930
  have eq2161 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1609 eq1935
    | exact resolve eq1935 eq1609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1609 eq1935
  have eq2182 : (σ (M.op x y)) = (M.op (σ x) (M.op (σ y) (σ y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2161
  have eq2290 : (σ y) = (M.op (M.op (σ y) (σ x)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2182 eq14
    | exact resolve eq14 eq2182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2608 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1813 eq2290
    | exact resolve eq2290 eq1813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1813 eq2290
  have eq2626 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq2608
  have eq2628 : (τ (σ y)) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2626 eq165
    | exact resolve eq165 eq2626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq165 eq2626
  have eq2642 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq2628
    | exact resolve eq2628 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2628
  have eq2646 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2642 eq640
    | exact resolve eq640 eq2642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640
  have eq2649 : y = (M.op (M.op x (M.op x y)) y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2642 eq56
    | exact resolve eq56 eq2642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2664 : (M.op x y) = (M.op y (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq2646
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2646
    | exact resolve eq2646 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2646
  have eq2768 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) X0) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2664 eq215
    | exact resolve eq215 eq2664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq2664
  have eq4341 : y = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2768 eq2642
    | exact resolve eq2642 eq2768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2642 eq2768
  have eq4392 : y = (M.op x (M.op x y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4341
  have eq4411 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4392 eq2649
    | exact resolve eq2649 eq4392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2649 eq4392
  have eq4441 : y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4411
  have eq4616 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq101
       have i₂ := eq4441
       grind)
    | exact superpose eq4441 eq101
    | exact resolve eq101 eq4441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101 eq4441
  have eq4635 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq4616
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq4616
    | exact resolve eq4616 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4616
  have eq4637 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4635 eq2182
    | exact resolve eq2182 eq4635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2182 eq4635
  have eq4658 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by grind
  clear eq4637
  have eq4662 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq4658
    | exact resolve eq4658 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4658
  have eq4663 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq4662
       have r₂ := eq28
       grind)
    | exact resolve eq4662 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4662
  have eq4665 : y = (τ (σ x)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq4663 eq30
    | exact resolve eq30 eq4663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4663
  have eq4698 : x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq4665
    | exact resolve eq4665 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4665
  have eq4699 : x = (M.op x y) ∨ x = y := by grind
  clear eq4698
  have eq4878 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq4699 eq21
    | exact resolve eq21 eq4699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4881 : ∀ X0 : G, y = (M.op (M.op x X0) (M.op X0 x)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq4699 eq56
    | exact resolve eq56 eq4699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq4699
  have eq4914 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq4878
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq4878
    | exact resolve eq4878 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4878
  have eq8118 : ∀ X0 : G, (σ (M.op x x)) = (M.op (M.op (σ (M.op x x)) X0) (M.op X0 (σ y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq430 (M.op x x) X0
       have i₂ := eq4881 x
       grind)
    | exact superpose eq4881 eq430
    | exact resolve eq430 eq4881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq4881
  have eq8149 : ∀ X0 : G, (σ (M.op x x)) = (M.op (M.op (σ (M.op x x)) X0) (M.op X0 (σ y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8118 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8118
    | (have j0 := eq8118 X0
       grind)
    | exact resolve eq8118 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8118
  have eq8165 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ x)) X0) (M.op X0 (σ y))) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8149 X0
       have i₂ := eq52
       grind)
    | exact superpose eq52 eq8149
    | exact resolve eq8149 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq8149
  have eq8169 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | (have i₁ := eq8165 x
       have i₂ := eq58 sF3 sF2 sF2 x
       grind)
    | exact superpose eq58 eq8165
    | exact resolve eq8165 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq8165
  have eq8170 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ x = y := by
    first
    | exact superpose eq27 eq8169
    | exact resolve eq8169 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8169
  have eq10056 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op X0 (M.op (M.op (M.op (σ x) X1) (M.op X1 X0)) (M.op (σ x) (σ x)))) ∨ x = y := by
    intro X0 X1
    first
    | exact superpose eq8170 eq738
    | exact resolve eq738 eq8170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8170
  have eq10070 : (σ x) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq10056 x x
       have i₂ := eq738 sF2 sF2 x x
       grind)
    | exact superpose eq738 eq10056
    | exact resolve eq10056 eq738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738 eq10056
  have eq10081 : (σ (M.op x y)) ≠ (σ x) ∨ x = y := by
    first
    | exact superpose eq10070 eq28
    | exact resolve eq28 eq10070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10070
  have eq10122 : x = y := by
    first
    | (have r₁ := eq10081
       have r₂ := eq4914
       grind)
    | exact resolve eq10081 eq4914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4914 eq10081
  have eq10123 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq10122
       grind)
    | exact superpose eq10122 eq19
    | exact resolve eq19 eq10122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq10124 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq10122
       grind)
    | exact superpose eq10122 eq25
    | exact resolve eq25 eq10122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq10122
  have eq10165 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq10124
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq10124
    | exact resolve eq10124 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq10124
  have eq10640 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq10165 eq27
    | exact resolve eq27 eq10165
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq10165
  have eq10764 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq10640 eq71
    | exact resolve eq71 eq10640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq10640
  have eq10826 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq10764
       have i₂ := eq10123
       grind)
    | exact superpose eq10123 eq10764
    | exact resolve eq10764 eq10123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10123 eq10764
  have eq10832 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq10826 eq15
    | exact resolve eq15 eq10826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10826
  have eq10874 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq10832
    | exact resolve eq10832 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq10832
  have eq10883 : False := by grind
  exact eq10883

/-- `Equation1662`: `x = (x ◇ y) ◇ ((y ◇ z) ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,X) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyx_y_pxy_pyx_Equation1662 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1662 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1662.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
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
  have eq114 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq47 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq47
    | (have j0 := eq47 x
       grind)
    | exact resolve eq47 eq22
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
  have eq116 : (k y (M.op x y)) = (τ (k (σ y) (σ (M.op x y)))) := by
    first
    | exact superpose eq20 eq47
    | (have j0 := eq47 (M.op x y)
       grind)
    | exact resolve eq47 eq20
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
  have eq174 : y ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq175 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op y X0) X0)) := by
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
  have eq177 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) = (M.op X0 (M.op (M.op (M.op (M.op X1 X2) X2) X3) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 X1) (M.op (M.op X1 X2) X2) X3
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq180 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (M.op (M.op (σ x) (σ y)) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op x (M.op (M.op y X1) X1))) = X0 := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X0 (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) X1)) := by
    intro X0 X1
    first
    | exact superpose eq180 eq16
    | exact resolve eq16 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq690 : ∀ X0 : G, (M.op (M.op X0 (M.op (M.op (σ x) (σ y)) (σ y))) (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq195 eq16
    | exact resolve eq16 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq785 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
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
  have eq787 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq922 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 (M.op (M.op X0 X0) X0)) ∨ (M.op (M.op X0 X0) X0) = (M.op X1 (M.op (M.op X0 X0) X0)) ∨ (M.op (M.op (M.op X0 X0) X0) X1) = (k (M.op (M.op X0 X0) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op (M.op X0 X0) X0) X1
       have i₂ := eq16 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq16 eq12
    | (have j0 := eq12 (M.op (M.op X0 X0) X0) X1
       grind)
    | (have r₁ := eq12 (M.op (M.op X1 x) x) (M.op (M.op (M.op (M.op X1 x) x) (M.op (M.op X1 x) x)) X1)
       have r₂ := eq16 (M.op (M.op (M.op X1 x) x) (M.op (M.op X1 x) x)) X1 x
       grind)
    | exact resolve eq12 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq923 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq978 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq785
       grind)
    | exact superpose eq785 eq39
    | exact resolve eq39 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq979 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq978
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq978
    | exact resolve eq978 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq981 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq979
    | exact resolve eq979 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979
  have eq989 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq981 eq787
    | exact resolve eq787 eq981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq996 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq989
       have r₂ := eq27
       grind)
    | exact resolve eq989 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq989
  have eq1007 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq996 eq16
    | exact resolve eq16 eq996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq1012 : (M.op x y) = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq177 eq1007
    | exact resolve eq1007 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1007
  have eq1020 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq16 y y X0
       have i₂ := eq1012
       grind)
    | exact superpose eq1012 eq16
    | exact resolve eq16 eq1012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1012
  have eq1025 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq176 eq1020
    | exact resolve eq1020 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1020
  have eq1027 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1025 eq175
    | (have r₁ := eq175
       have r₂ := eq1025
       grind)
    | exact resolve eq175 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1028 : ∀ X0 : G, (σ x) = (M.op (σ y) (M.op (M.op (σ y) X0) X0)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq1025 eq177
    | exact resolve eq177 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025
  have eq1034 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1027
  have eq1047 : (σ (M.op x y)) = (σ x) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1034 eq981
    | exact resolve eq981 eq1034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq1050 : (τ (σ x)) = (k y (τ (σ x))) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1034 eq107
    | exact resolve eq107 eq1034
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1034
  have eq1052 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1047
  have eq1055 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq1050
    | exact resolve eq1050 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1050
  have eq1058 : x = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq1055
       have r₂ := eq174
       grind)
    | exact resolve eq1055 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1055
  have eq1063 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq1058
       grind)
    | exact superpose eq1058 eq36
    | exact resolve eq36 eq1058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq1066 : (σ x) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1063
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1063
    | exact resolve eq1063 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1063
  have eq1152 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq16 y y X0
       have i₂ := eq1052
       grind)
    | exact superpose eq1052 eq16
    | exact resolve eq16 eq1052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1052
  have eq1157 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq176 eq1152
    | exact resolve eq1152 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152
  have eq1158 : (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1157
  have eq1160 : y = (τ (σ x)) ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1158 eq31
    | exact resolve eq31 eq1158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1158
  have eq1194 : x = y ∨ (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq1160
    | exact resolve eq1160 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1160
  have eq1195 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq1194
  have eq1198 : (M.op x y) = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq1195 eq28
    | exact resolve eq28 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1202 : (k y (M.op x y)) = (τ (k (σ y) (σ x))) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq1195 eq116
    | exact resolve eq116 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq1215 : (k y x) = (k y (M.op x y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq114 eq1202
    | exact resolve eq1202 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq1202
  have eq1219 : y = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq1198
    | exact resolve eq1198 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1198
  have eq1223 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq1219
       grind)
    | exact superpose eq1219 eq24
    | exact resolve eq24 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1227 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (M.op (M.op x y) X0) X0)) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq176 X0
       have i₂ := eq1219
       grind)
    | exact superpose eq1219 eq176
    | exact resolve eq176 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1239 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq1223
    | exact resolve eq1223 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1223
  have eq1320 : (M.op x y) = (k y (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq785
       have i₂ := eq1215
       grind)
    | exact superpose eq1215 eq785
    | exact resolve eq785 eq1215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq785 eq1215
  have eq1323 : (M.op x y) = (k y (M.op x y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq1320
  have eq1402 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X1) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X0 (M.op (M.op X1 X2) X2) x
       have i₂ := eq178 (M.op X0 (M.op (M.op X1 X2) X2)) X1 X2 x
       grind)
    | exact superpose eq178 eq16
    | exact resolve eq16 eq178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq2101 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1323 eq36
    | exact resolve eq36 eq1323
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1323
  have eq2108 : (σ (M.op x y)) = (k (σ y) (σ (M.op x y))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq20 eq2101
    | exact resolve eq2101 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2101
  have eq2110 : (σ x) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1195 eq2108
    | exact resolve eq2108 eq1195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq2108
  have eq2118 : (τ (σ x)) = (k y (τ (σ x))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq2110 eq107
    | exact resolve eq107 eq2110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq2110
  have eq2124 : x = (k y x) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq2118
    | exact resolve eq2118 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2118
  have eq2127 : (M.op x y) = (M.op y y) ∨ x = (k y x) ∨ x = y := by
    first
    | (have r₁ := eq2124
       have r₂ := eq174
       grind)
    | exact resolve eq2124 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2124
  have eq2138 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y X0) X0)) ∨ x = (k y x) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq16 y y X0
       have i₂ := eq2127
       grind)
    | exact superpose eq2127 eq16
    | exact resolve eq16 eq2127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127
  have eq2146 : x = y ∨ x = (k y x) ∨ x = y := by
    first
    | exact superpose eq176 eq2138
    | exact resolve eq2138 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2138
  have eq2147 : x = (k y x) ∨ x = y := by grind
  clear eq2146
  have eq2161 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq2147
       grind)
    | exact superpose eq2147 eq36
    | exact resolve eq36 eq2147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq2147
  have eq2175 : (σ x) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq2161
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2161
    | exact resolve eq2161 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2161
  have eq2184 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq2175 eq787
    | exact resolve eq787 eq2175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787 eq2175
  have eq2216 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) X0) X0)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq2184 eq16
    | exact resolve eq16 eq2184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2184
  have eq2226 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq177 eq2216
    | exact resolve eq2216 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216
  have eq2227 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2226 eq27
    | exact resolve eq27 eq2226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2226
  have eq2241 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1239 eq2227
    | (have r₁ := eq2227
       have r₂ := eq1239
       grind)
    | exact resolve eq2227 eq1239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2227
  have eq2244 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2241
  have eq2245 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq2244
  have eq2348 : ∀ X0 : G, (σ x) = (M.op (σ x) (M.op (M.op (σ y) X0) X0)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2245 eq177
    | exact resolve eq177 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq2353 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2245 eq690
    | exact resolve eq690 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq2358 : ∀ X0 : G, (M.op (M.op X0 (M.op (σ x) (σ y))) (σ x)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq26 eq2353
    | (have j0 := eq2353 X0
       grind)
    | exact resolve eq2353 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2353
  have eq2363 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq2245 eq2358
    | exact resolve eq2358 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2358
  have eq2810 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3⟩ := hcon
    have f2810_16 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
      intro X0
      grind
    have f2810_24 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X1 X2) X2)) = X0 := by
      intro X0 X1 X2
      grind
    have f2810_25 : X1 ≠ (M.op (M.op X1 X0) X0) := by grind
    have f2810_26 : (σ x) ≠ (σ y) := by grind
    have f2810_27 : x ≠ y := by grind
    have f2810_28 : x ≠ (M.op x y) := by grind
    have f2810_29 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ x = y ∨ x = (M.op x y) := by
      intro X0
      first
      | (have j0 := f2810_16 X0
         grind)
      | (have r₁ := f2810_16 X0
         have r₂ := f2810_26
         grind)
      | exact resolve f2810_16 f2810_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2810_30 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 ∨ x = (M.op x y) := by
      intro X0
      first
      | (have j0 := f2810_29 X0
         grind)
      | (have r₁ := f2810_29 X0
         have r₂ := f2810_27
         grind)
      | exact resolve f2810_29 f2810_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2810_31 : ∀ X0 : G, (M.op (M.op X0 (σ x)) (σ x)) = X0 := by
      intro X0
      first
      | (have j0 := f2810_30 X0
         grind)
      | (have r₁ := f2810_30 X0
         have r₂ := f2810_28
         grind)
      | exact resolve f2810_30 f2810_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2810_43 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 := by
      intro X0 X1
      first
      | (have i₁ := f2810_24 X1 X0 (σ x)
         have i₂ := f2810_31 X0
         grind)
      | exact superpose f2810_31 f2810_24
      | exact resolve f2810_24 f2810_31
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2810_49 : X1 ≠ X1 := by
      first
      | (have i₁ := f2810_25
         have i₂ := f2810_43 X0 X1
         grind)
      | exact superpose f2810_43 f2810_25
      | (have r₁ := f2810_25
         have r₂ := f2810_43 X0 X1
         grind)
      | exact resolve f2810_25 f2810_43
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f2810_53 : False := by grind
    exact f2810_53
  have eq2817 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2363 eq1227
    | exact resolve eq1227 eq2363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227 eq2363
  have eq2831 : x = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq2817
  have eq2863 : x ≠ x ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2831 eq12
    | exact resolve eq12 eq2831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2831
  have eq2870 : x ≠ x ∨ x = (M.op x y) ∨ x = (k (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2863
  have eq2871 : x = (k (M.op x y) (M.op x y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq2870
  have eq2889 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2871 eq41
    | exact resolve eq41 eq2871
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq2871
  have eq2893 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20 eq2889
    | exact resolve eq2889 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2889
  have eq2895 : (σ x) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2893
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2893
    | exact resolve eq2893 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2893
  have eq2897 : (σ x) = (k (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1239 eq2895
    | exact resolve eq2895 eq1239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1239 eq2895
  have eq7765 : (σ x) = (M.op (σ x) (M.op (k (σ y) (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq2348 sF3
       have i₂ := eq923 sF3
       grind)
    | exact superpose eq923 eq2348
    | (have j1 := eq923 (σ y)
       grind)
    | exact resolve eq2348 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7878 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2897 eq7765
    | exact resolve eq7765 eq2897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7765
  have eq7898 : (σ x) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq7878
    | exact resolve eq7878 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7878
  have eq7907 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2245 eq7898
    | exact resolve eq7898 eq2245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2245 eq7898
  have eq10153 : (σ x) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (M.op (σ y) (σ y)) (σ y)) ∨ (M.op (M.op (M.op (σ y) (σ y)) (σ y)) (σ x)) = (k (M.op (M.op (σ y) (σ y)) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2348 eq922
    | (have j0 := eq922 (σ y) (σ x)
       grind)
    | exact resolve eq922 eq2348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq922 eq2348
  have eq10158 : (σ x) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (M.op (M.op (σ y) (σ y)) (σ y)) (σ x)) = (k (M.op (M.op (σ y) (σ y)) (σ y)) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2810 eq10153
    | exact resolve eq10153 eq2810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10153
  have eq10159 : (σ x) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (M.op (M.op (σ y) (σ y)) (σ y)) (σ x)) = (k (M.op (M.op (σ y) (σ y)) (σ y)) (σ x)) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq10158
  have eq10205 : (σ x) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq2810 eq10159
    | exact resolve eq10159 eq2810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10159
  have eq10244 : (σ x) ≠ (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1066 eq10205
    | exact resolve eq10205 eq1066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1066 eq10205
  have eq14817 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq7907 eq13
    | (have j0 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq7907
       grind)
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq7907
       grind)
    | exact resolve eq13 eq7907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7907
  have eq14845 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq14817
  have eq14891 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2897 eq14845
    | exact resolve eq14845 eq2897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14845
  have eq14892 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq14891
  have eq15208 : (σ x) ≠ (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq10244
       have i₂ := eq923 sF3
       grind)
    | exact superpose eq923 eq10244
    | (have j1 := eq923 (σ y)
       grind)
    | exact resolve eq10244 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10244
  have eq15220 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq15208
       have r₂ := eq2897
       grind)
    | exact resolve eq15208 eq2897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15208
  have eq15368 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq15220 eq13
    | (have j0 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq15220
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq15220
       grind)
    | exact resolve eq13 eq15220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15220
  have eq15396 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq15368
  have eq15443 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq2897 eq15396
    | exact resolve eq15396 eq2897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2897 eq15396
  have eq15444 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq15443
  have eq15492 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq15444 eq2810
    | exact resolve eq2810 eq15444
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2810 eq15444
  have eq15503 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq15492
  have eq15523 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq14892 eq15503
    | exact resolve eq15503 eq14892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14892 eq15503
  have eq15524 : (σ x) = (σ y) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq15523
  have eq15550 : y = (τ (σ x)) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq15524 eq31
    | exact resolve eq31 eq15524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15524
  have eq15633 : x = y ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq15550
    | exact resolve eq15550 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15550
  have eq15634 : x = (M.op x y) ∨ x = y := by grind
  clear eq15633
  have eq15647 : (M.op x y) = (M.op (M.op x y) y) ∨ x = y := by
    first
    | (have i₁ := eq18
       have i₂ := eq15634
       grind)
    | exact superpose eq15634 eq18
    | exact resolve eq18 eq15634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15652 : ∀ X0 X1 : G, (M.op (M.op X0 (M.op x y)) (M.op (M.op x y) (M.op (M.op y X1) X1))) = X0 ∨ x = y := by
    intro X0 X1
    first
    | (have i₁ := eq183 X0 X1
       have i₂ := eq15634
       grind)
    | exact superpose eq15634 eq183
    | exact resolve eq183 eq15634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq15682 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) x) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq176 eq15652
    | exact resolve eq15652 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq15652
  have eq15686 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq15634 eq15682
    | exact resolve eq15682 eq15634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15682
  have eq15966 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 ∨ x = y := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f15966_13 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op (M.op X1 X2) X2)) X1) = X0 := by
      intro X0 X1 X2
      grind
    have f15966_14 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = X0 ∨ x = y := by
      intro X0
      grind
    have f15966_23 : X1 ≠ (M.op (M.op X1 X0) X0) := by grind
    have f15966_24 : x ≠ y := by grind
    have f15966_25 : ∀ X0 : G, (M.op (M.op X0 (M.op x y)) (M.op x y)) = X0 := by
      intro X0
      first
      | (have j0 := f15966_14 X0
         grind)
      | (have r₁ := f15966_14 X0
         have r₂ := f15966_24
         grind)
      | exact resolve f15966_14 f15966_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f15966_51 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = X1 := by
      intro X0 X1
      first
      | (have i₁ := f15966_13 X1 X0 (M.op x y)
         have i₂ := f15966_25 X0
         grind)
      | exact superpose f15966_25 f15966_13
      | exact resolve f15966_13 f15966_25
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f15966_65 : X1 ≠ X1 := by
      first
      | (have i₁ := f15966_23
         have i₂ := f15966_51 X0 X1
         grind)
      | exact superpose f15966_51 f15966_23
      | (have r₁ := f15966_23
         have r₂ := f15966_51 X0 X1
         grind)
      | exact resolve f15966_23 f15966_51
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f15966_66 : False := by grind
    exact f15966_66
  clear eq1402
  have eq15986 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq15686 eq1028
    | exact resolve eq1028 eq15686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028 eq15686
  have eq16012 : (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq15986
  have eq16142 : ∀ X0 : G, (M.op (k X0 X0) X0) = X0 ∨ x = y ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq15966 X0 X0
       have i₂ := eq923 X0
       grind)
    | exact superpose eq923 eq15966
    | (have j1 := eq923 X0
       grind)
    | exact resolve eq15966 eq923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq923 eq15966
  have eq18793 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq16012 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq16012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16012
  have eq18824 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ y)) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq18793
  have eq18825 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq18824
  have eq19248 : (τ (σ x)) = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq18825 eq115
    | exact resolve eq115 eq18825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq18825
  have eq19269 : x = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq19248
    | exact resolve eq19248 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19248
  have eq19272 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq1219 eq19269
    | exact resolve eq19269 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219 eq19269
  have eq21465 : y = (M.op (M.op x y) y) ∨ x = y ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16142 y
       have i₂ := eq19272
       grind)
    | exact superpose eq19272 eq16142
    | (have j0 := eq16142 y
       grind)
    | exact resolve eq16142 eq19272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16142
  have eq21705 : y = (M.op (M.op x y) y) ∨ x = y ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq21465
  have eq21779 : y = (M.op x y) ∨ x = y ∨ y = (M.op y y) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq15647 eq21705
    | exact resolve eq21705 eq15647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15647 eq21705
  have eq21780 : y = (M.op y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq21779
  have eq21875 : y ≠ y ∨ y = (k y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq21780
       grind)
    | exact superpose eq21780 eq13
    | (have j0 := eq13 y y
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq21780
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq21780
       grind)
    | exact resolve eq13 eq21780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21780
  have eq21907 : y = (k y y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq21875
  have eq21937 : y = (M.op x y) ∨ x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq19272 eq21907
    | exact resolve eq21907 eq19272
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19272 eq21907
  have eq21938 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by grind
  clear eq21937
  have eq21952 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq21938 eq31
    | exact resolve eq31 eq21938
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq21938
  have eq22064 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq21952
    | exact resolve eq21952 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21952
  have eq22065 : y = (M.op x y) ∨ x = y := by grind
  clear eq22064
  have eq22192 : x ≠ (M.op x y) ∨ x = y := by grind
  clear eq22065
  have eq22194 : x = y := by
    first
    | (have r₁ := eq22192
       have r₂ := eq15634
       grind)
    | exact resolve eq22192 eq15634
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15634 eq22192
  have eq22208 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq22194
       grind)
    | exact superpose eq22194 eq18
    | exact resolve eq18 eq22194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq22209 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq22194
       grind)
    | exact superpose eq22194 eq24
    | exact resolve eq24 eq22194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq22212 : x ≠ (M.op x y) ∨ x = (k x x) := by
    first
    | (have i₁ := eq174
       have i₂ := eq22194
       grind)
    | exact superpose eq22194 eq174
    | exact resolve eq174 eq22194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq22194
  have eq22231 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq22209
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22209
    | exact resolve eq22209 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22209
  have eq22235 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq22231 eq26
    | exact resolve eq26 eq22231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq22231
  have eq22338 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq12 x x
       have i₂ := eq22208
       grind)
    | exact superpose eq22208 eq12
    | exact resolve eq12 eq22208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22208
  have eq22361 : (M.op x y) = (k x x) ∨ x = (M.op x y) := by grind
  clear eq22338
  have eq22406 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq22235 eq12
    | exact resolve eq12 eq22235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22407 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq22235 eq13
    | (have j0 := eq13 (σ x) (σ x)
       grind)
    | exact resolve eq13 eq22235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22235
  have eq22429 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22406
  have eq22582 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq22361
       grind)
    | exact superpose eq22361 eq39
    | exact resolve eq39 eq22361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq22361
  have eq22589 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22582
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq22582
    | exact resolve eq22582 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22582
  have eq22591 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq22589
    | exact resolve eq22589 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22589
  have eq22666 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22591 eq22429
    | exact resolve eq22429 eq22591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22682 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22666
       have r₂ := eq27
       grind)
    | exact resolve eq22666 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22666
  have eq22691 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22682 eq27
    | exact resolve eq27 eq22682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22725 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22682 eq22407
    | (have r₁ := eq22407
       have r₂ := eq22682
       grind)
    | exact resolve eq22407 eq22682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22407 eq22682
  have eq22726 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq22725
  have eq22792 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22726 eq22591
    | exact resolve eq22591 eq22726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22591
  have eq22794 : (τ (σ x)) = (k (τ (σ x)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq22726 eq141
    | exact resolve eq141 eq22726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq22726
  have eq22799 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq22792
  have eq22816 : x = (k x x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq29 eq22794
    | exact resolve eq22794 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq22794
  have eq22818 : x = (M.op x y) := by
    first
    | (have r₁ := eq22799
       have r₂ := eq22691
       grind)
    | exact resolve eq22799 eq22691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22691 eq22799
  have eq22827 : x = (k x x) := by
    first
    | (have r₁ := eq22816
       have r₂ := eq22212
       grind)
    | exact resolve eq22816 eq22212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22212 eq22816
  have eq22830 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq22827
       have i₂ := eq22818
       grind)
    | exact superpose eq22818 eq22827
    | exact resolve eq22827 eq22818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22827
  have eq22834 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq22818
       grind)
    | exact superpose eq22818 eq22
    | exact resolve eq22 eq22818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq22818
  have eq22902 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq22834 eq20
    | exact resolve eq20 eq22834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22834
  have eq23084 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq22830 eq37
    | exact resolve eq37 eq22830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq22830
  have eq23094 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq23084
    | exact resolve eq23084 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq23084
  have eq23096 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq22902 eq23094
    | exact resolve eq23094 eq22902
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23094
  have eq23197 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq23096 eq22429
    | exact resolve eq22429 eq23096
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22429 eq23096
  have eq23205 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq23197
  have eq23226 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq23205 eq27
    | exact resolve eq27 eq23205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq23205
  have eq23278 : False := by grind
  exact eq23278

/-- `Equation1701`: `x = (y ◇ x) ◇ ((z ◇ x) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = m(X,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_pxy_pxy_pxx_pxy_Equation1701 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law1701 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1701.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) ≠ X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X1) = X0 := by
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
  have eq87 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq329 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq87 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X0)
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X1)
       have r₂ := eq87 X1 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq87 X0 X1
       grind)
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq335 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq336 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq329 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq329
  have eq337 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq336 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq339 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq337 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq337
    | (have j0 := eq337 X0 X1
       grind)
    | exact resolve eq337 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq343 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq339 X0 X1
       have j1 := eq335 X0 X1
       grind)
    | (have r₁ := eq339 X0 X1
       have r₂ := eq335 X0 X1
       grind)
    | (have r₁ := eq339 (k X0 X1) X0
       have r₂ := eq335 X0 X1
       grind)
    | (have r₁ := eq339 X0 X0
       have r₂ := eq335 X0 X0
       grind)
    | exact resolve eq339 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335 eq339
  have eq600 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq343 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq343
    | exact resolve eq343 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq343 x y
       grind)
    | exact superpose eq343 eq16
    | (have j1 := eq343 x y
       grind)
    | exact resolve eq16 eq343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq343
  have eq626 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq600 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq600
    | (have j0 := eq600 X0 X1
       grind)
    | exact resolve eq600 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq600
  have eq632 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq626 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq626
    | exact resolve eq626 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq716 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq632 (τ X0) X1
       grind)
    | exact superpose eq632 eq18
    | (have j1 := eq632 (τ X0) X1
       grind)
    | exact resolve eq18 eq632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq632
  have eq933 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq716 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq716
    | exact resolve eq716 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq716
  have eq988 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq933 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq933
    | (have j0 := eq933 X0 X1
       grind)
    | exact resolve eq933 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq933
  have eq1100 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq608
       have i₂ := eq988 x y
       grind)
    | exact superpose eq988 eq608
    | (have j1 := eq988 (σ x) (σ y)
       grind)
    | (have r₁ := eq608
       have r₂ := eq988 x y
       grind)
    | exact resolve eq608 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1101 : x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1100
  have eq1113 : (M.op x y) = (k x y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1101
  have eq1127 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq608
       have i₂ := eq1113
       grind)
    | exact superpose eq1113 eq608
    | exact resolve eq608 eq1113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq1113
  have eq1128 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1127
  have eq1129 : (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq1128
  have eq1141 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) := by grind
  clear eq1129
  have eq1156 : (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq1141
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq1141
    | exact resolve eq1141 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1141
  have eq1162 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1156
       grind)
    | exact superpose eq1156 eq16
    | exact resolve eq16 eq1156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1156
  have eq1224 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1162
       have i₂ := eq988 x y
       grind)
    | exact superpose eq988 eq1162
    | (have j1 := eq988 x y
       grind)
    | (have r₁ := eq1162
       have r₂ := eq988 x y
       grind)
    | exact resolve eq1162 eq988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq988
  have eq1225 : x = (M.op y y) := by grind
  clear eq1224
  have eq1230 : (M.op x y) = (k x y) := by grind
  clear eq1225
  have eq1281 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1162
       have i₂ := eq1230
       grind)
    | exact superpose eq1230 eq1162
    | exact resolve eq1162 eq1230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162 eq1230
  have eq1284 : False := by grind
  exact eq1284

/-- `Equation1724`: `x = (y ◇ y) ◇ ((x ◇ z) ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_y_pxy_pyy_pxy_Equation1724 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1724 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1724.models_iff G M).mp hM
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
  have eq9 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq10 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq11 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq12 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op (M.op X0 X2) X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq16 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12
    | exact resolve eq12 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq12
    | exact resolve eq12 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k X0 (τ X1))
       have i₂ := eq17 X1 X0
       grind)
    | exact superpose eq17 eq9
    | exact resolve eq9 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq25 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq9
    | exact resolve eq9 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (k (τ X0) (τ X1)) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq21 (τ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq21
    | exact resolve eq21 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq183 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (τ (k X0 (σ X1))) ∨ (M.op X1 (τ X0)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op (τ X0) X1)
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq9
    | (have j1 := eq25 X0 X1
       grind)
    | exact resolve eq9 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq201 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op X1 (τ X0)) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq183 X0 X1
       have i₂ := eq28 X0 X1
       grind)
    | exact superpose eq28 eq183
    | (have j0 := eq183 X0 X1
       grind)
    | exact resolve eq183 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq205 : ∀ X0 X1 : G, (k (τ X0) X1) = (M.op (τ X0) X1) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq201 X0 X1
       have j1 := eq16 (τ X0) X1
       grind)
    | (have r₁ := eq201 X0 (τ X0)
       have r₂ := eq16 X0 (τ X0)
       grind)
    | (have r₁ := eq201 X0 X1
       have r₂ := eq16 X0 X1
       grind)
    | exact resolve eq201 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq201
  have eq359 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq205 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq205
    | exact resolve eq205 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq367 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 (τ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq205 X0 X1
       grind)
    | exact superpose eq205 eq18
    | (have j1 := eq205 X0 X1
       grind)
    | exact resolve eq18 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X1
       have i₂ := eq205 X0 (τ X1)
       grind)
    | exact superpose eq205 eq33
    | (have j1 := eq205 X0 (τ X1)
       grind)
    | exact resolve eq33 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq205
  have eq406 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X0 X1
       have i₂ := eq359 X0 (σ X1)
       grind)
    | exact superpose eq359 eq28
    | (have j1 := eq359 X0 (σ X1)
       grind)
    | exact resolve eq28 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq410 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq359 (σ X0) (σ X1)
       grind)
    | exact superpose eq359 eq12
    | (have j1 := eq359 (σ X0) (σ X1)
       grind)
    | exact resolve eq12 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq469 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq367 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq367
    | exact resolve eq367 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367
  have eq506 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq469 X0 X1
       have i₂ := eq12 X0 X1
       grind)
    | exact superpose eq12 eq469
    | (have j0 := eq469 X0 X1
       grind)
    | exact resolve eq469 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq1209 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (τ X0)
       have i₂ := eq368 X0 X0
       grind)
    | exact superpose eq368 eq16
    | (have j0 := eq16 X1 (τ X0)
       have j1 := eq368 X0 X0
       grind)
    | (have r₁ := eq16 X0 (τ X0)
       have r₂ := eq368 X0 X0
       grind)
    | exact resolve eq16 eq368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1213 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq368 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq1219 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (k X1 (τ X0)) = (M.op X1 (τ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1209 X0 X1
       have j1 := eq16 X1 (τ X0)
       grind)
    | (have r₁ := eq1209 X0 X1
       have r₂ := eq16 X0 (τ X0)
       grind)
    | exact resolve eq1209 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1209
  have eq2308 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq11
       have i₂ := eq410 x y
       grind)
    | exact superpose eq410 eq11
    | (have j1 := eq410 x y
       grind)
    | exact resolve eq11 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410
  have eq2428 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2308
       have i₂ := eq506 x y
       grind)
    | exact superpose eq506 eq2308
    | (have j1 := eq506 (σ x) (σ y)
       grind)
    | (have r₁ := eq2308
       have r₂ := eq506 x y
       grind)
    | exact resolve eq2308 eq506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq506
  have eq2431 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq2428
  have eq2540 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ y) (σ y))) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq13 (σ y) X0 (σ x)
       have i₂ := eq2431
       grind)
    | exact superpose eq2431 eq13
    | exact resolve eq13 eq2431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2631 : ∀ X0 X1 : G, (M.op (σ y) (M.op (M.op X0 X1) X0)) = X0 ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op (σ y) (σ y)) X1
       have i₂ := eq2540 (σ y)
       grind)
    | exact superpose eq2540 eq13
    | exact resolve eq13 eq2540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2713 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (σ y) X0) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq2631 (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)
       have i₂ := eq13 X0 (M.op (M.op X0 X1) X0) X1
       grind)
    | exact superpose eq13 eq2631
    | exact resolve eq2631 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2838 : ∀ X0 X1 : G, (M.op (σ y) (M.op X1 X1)) = (M.op X0 (M.op X1 X1)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq2713 (M.op X1 X1) (M.op (M.op X0 x) X0)
       have i₂ := eq13 X0 X1 x
       grind)
    | exact superpose eq13 eq2713
    | exact resolve eq2713 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2842 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2713 (σ y) (M.op (M.op X0 x) X0)
       have i₂ := eq2631 X0 x
       grind)
    | exact superpose eq2631 eq2713
    | exact resolve eq2713 eq2631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2845 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = X0 ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2631 X0 x
       have i₂ := eq2713 X0 x
       grind)
    | exact superpose eq2713 eq2631
    | exact resolve eq2631 eq2713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2846 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op (σ y) X0)) = X0 ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1 x
       have i₂ := eq2713 X0 x
       grind)
    | exact superpose eq2713 eq13
    | exact resolve eq13 eq2713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2858 : ∀ X0 : G, (M.op (σ y) (M.op (σ y) X0)) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq2845 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2845
  have eq2860 : ∀ X0 : G, (M.op (σ y) (σ y)) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq2842 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2842
  have eq2979 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2858 (σ x)
       have i₂ := eq2431
       grind)
    | exact superpose eq2431 eq2858
    | exact resolve eq2858 eq2431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2993 : (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq2979
  have eq3089 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2540 X0
       have i₂ := eq2993
       grind)
    | exact superpose eq2993 eq2540
    | exact resolve eq2540 eq2993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2540
  have eq3101 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2713 (σ y) (σ y)
       have i₂ := eq2993
       grind)
    | exact superpose eq2993 eq2713
    | exact resolve eq2713 eq2993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3106 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq3101
  have eq3113 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq3089 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3089
  have eq3221 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq11
       have i₂ := eq3106
       grind)
    | exact superpose eq3106 eq11
    | exact resolve eq11 eq3106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4006 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = X0 ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2846 X0 (σ y)
       have i₂ := eq2993
       grind)
    | exact superpose eq2993 eq2846
    | exact resolve eq2846 eq2993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4016 : ∀ X0 X1 : G, (M.op (σ y) X0) = (M.op (M.op X1 X1) X0) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op (σ y) X0) X1 (M.op (σ y) X0)
       have i₂ := eq2846 X0 (M.op (σ y) X0)
       grind)
    | exact superpose eq2846 eq13
    | exact resolve eq13 eq2846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2846
  have eq4039 : ∀ X0 : G, (M.op (σ x) (M.op (σ y) X0)) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq4006 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4006
  have eq4204 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq4039 (M.op (σ y) X0)
       have i₂ := eq2858 X0
       grind)
    | exact superpose eq2858 eq4039
    | exact resolve eq4039 eq2858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2858
  have eq4210 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op X0 (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2713 (σ x) (M.op (σ y) X0)
       have i₂ := eq4039 X0
       grind)
    | exact superpose eq4039 eq2713
    | exact resolve eq2713 eq4039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2713
  have eq4215 : ∀ X0 : G, (M.op (σ y) (σ x)) = (M.op X0 (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq4210 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4210
  have eq4217 : ∀ X0 : G, (M.op (σ y) X0) = (M.op (σ x) X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq4204 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4204
  have eq4337 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq4039 X0
       have i₂ := eq4217 X0
       grind)
    | exact superpose eq4217 eq4039
    | exact resolve eq4039 eq4217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4217
  have eq4383 : ∀ X0 : G, (M.op (σ x) (M.op (σ x) X0)) = X0 ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq4337 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4337
  have eq4872 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq2860 X1
       have i₂ := eq2860 X0
       grind)
    | (have i₁ := eq2860 X0
       have i₂ := eq2860 (σ y)
       grind)
    | exact superpose eq2860 eq2860
    | exact resolve eq2860 eq2860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4878 : ∀ X0 : G, (σ x) = (M.op X0 (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2993
       have i₂ := eq2860 X0
       grind)
    | (have i₁ := eq2993
       have i₂ := eq2860 (σ y)
       grind)
    | exact superpose eq2860 eq2993
    | exact resolve eq2993 eq2860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2860 eq2993
  have eq4951 : ∀ X0 : G, (σ x) = (M.op X0 (σ y)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq4878 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4878
  have eq4955 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have j0 := eq4872 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4872
  have eq5095 : ∀ X0 : G, (τ (σ x)) = (k (τ X0) y) ∨ (σ y) = (M.op (σ y) X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq406 X0 y
       have i₂ := eq4951 X0
       grind)
    | exact superpose eq4951 eq406
    | (have j0 := eq406 X0 y
       grind)
    | exact resolve eq406 eq4951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4951
  have eq5157 : ∀ X0 : G, (σ y) = (M.op (σ y) X0) ∨ x = (k (τ X0) y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq5095 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq5095
    | (have j0 := eq5095 X0
       grind)
    | exact resolve eq5095 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5095
  have eq5937 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op X0 X0)) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq3113 (M.op X0 X0)
       have i₂ := eq4016 (M.op X0 X0) X0
       grind)
    | exact superpose eq4016 eq3113
    | exact resolve eq3113 eq4016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3113 eq4016
  have eq5962 : ∀ X0 : G, (σ y) = (M.op (M.op (σ y) (M.op X0 X0)) (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq5937 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5937
  have eq7039 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X1 (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq4215 X1
       have i₂ := eq4215 X0
       grind)
    | (have i₁ := eq4215 X0
       have i₂ := eq4215 (σ y)
       grind)
    | exact superpose eq4215 eq4215
    | exact resolve eq4215 eq4215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7045 : ∀ X0 : G, (σ y) = (M.op X0 (σ x)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2431
       have i₂ := eq4215 X0
       grind)
    | (have i₁ := eq2431
       have i₂ := eq4215 (σ y)
       grind)
    | exact superpose eq4215 eq2431
    | exact resolve eq2431 eq4215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2431 eq4215
  have eq7109 : ∀ X0 : G, (σ y) = (M.op X0 (σ x)) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq7045 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7045
  have eq7113 : ∀ X0 X1 : G, (M.op X0 (σ x)) = (M.op X1 (σ x)) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have j0 := eq7039 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7039
  have eq7337 : ∀ X0 : G, (τ (σ y)) = (k (τ X0) x) ∨ (σ x) = (M.op (σ x) X0) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq406 X0 x
       have i₂ := eq7109 X0
       grind)
    | exact superpose eq7109 eq406
    | (have j0 := eq406 X0 x
       grind)
    | exact resolve eq406 eq7109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq406 eq7109
  have eq7403 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ y = (k (τ X0) x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq7337 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq7337
    | (have j0 := eq7337 X0
       grind)
    | exact resolve eq7337 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7337
  have eq23216 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2838 X2 X1
       have i₂ := eq2838 X0 X1
       grind)
    | (have i₁ := eq2838 X0 X1
       have i₂ := eq2838 (σ y) X1
       grind)
    | exact superpose eq2838 eq2838
    | exact resolve eq2838 eq2838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2838
  have eq23526 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) ∨ y = (M.op y x) := by
    intro X0 X1 X2
    first
    | (have j0 := eq23216 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23216
  have eq88083 : ∀ X0 : G, (M.op (σ x) (σ y)) = X0 ∨ y = (M.op y x) ∨ x = (k (τ X0) y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq4039 X0
       have i₂ := eq5157 X0
       grind)
    | exact superpose eq5157 eq4039
    | (have j1 := eq5157 X0
       grind)
    | exact resolve eq4039 eq5157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4039
  have eq88139 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k X0 (σ y)) ∨ x = (k (τ (σ y)) y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq16 X0 (σ y)
       have i₂ := eq5157 (σ y)
       grind)
    | exact superpose eq5157 eq16
    | (have j0 := eq16 X0 (σ y)
       have j1 := eq5157 (σ y)
       grind)
    | (have r₁ := eq16 X0 (σ y)
       have r₂ := eq5157 (σ y)
       grind)
    | exact resolve eq16 eq5157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5157
  have eq88433 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ x = (k (τ (σ y)) y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq88139 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88139
  have eq88472 : ∀ X0 : G, (M.op (σ x) (σ y)) = X0 ∨ y = (M.op y x) ∨ x = (k (τ X0) y) := by
    intro X0
    first
    | (have j0 := eq88083 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88083
  have eq88529 : ∀ X0 : G, (M.op X0 (σ y)) = (k X0 (σ y)) ∨ x = (k y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq88433 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq88433
    | (have j0 := eq88433 X0
       grind)
    | exact resolve eq88433 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88433
  have eq121180 : ∀ X0 X1 : G, (M.op X1 (σ y)) = X0 ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ x = (k (τ X0) y) := by
    intro X0 X1
    first
    | (have i₁ := eq4955 X1 (σ x)
       have i₂ := eq88472 X0
       grind)
    | (have i₁ := eq4955 X0 X1
       have i₂ := eq88472 (M.op X1 (σ y))
       grind)
    | exact superpose eq88472 eq4955
    | (have j1 := eq88472 X0
       grind)
    | exact resolve eq4955 eq88472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4955 eq88472
  have eq121273 : ∀ X0 X1 : G, x = (k (τ X0) y) ∨ y = (M.op y x) ∨ (M.op X1 (σ y)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq121180 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121180
  have eq127738 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ y)) ∨ y = (M.op y x) ∨ x = (k X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq121273 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq121273
    | (have j0 := eq121273 (σ X0) X1
       grind)
    | exact resolve eq121273 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121273
  have eq130598 : ∀ X0 X1 : G, (τ (M.op X0 (σ y))) = X1 ∨ y = (M.op y x) ∨ x = (k X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq127738 X1 X0
       grind)
    | exact superpose eq127738 eq9
    | (have j1 := eq127738 X1 X1
       grind)
    | exact resolve eq9 eq127738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127738
  have eq133599 : ∀ X0 : G, (τ (σ x)) = X0 ∨ y = (M.op y x) ∨ x = (k X0 y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq130598 (σ x) X0
       have i₂ := eq3106
       grind)
    | exact superpose eq3106 eq130598
    | (have j0 := eq130598 X0 X0
       grind)
    | exact resolve eq130598 eq3106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3106
  have eq133975 : ∀ X0 : G, (τ (σ x)) = X0 ∨ y = (M.op y x) ∨ x = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq133599 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133599
  have eq134045 : ∀ X0 : G, y = (M.op y x) ∨ x = X0 ∨ x = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq133975 X0
       have i₂ := eq9 x
       grind)
    | exact superpose eq9 eq133975
    | (have j0 := eq133975 X0
       grind)
    | exact resolve eq133975 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133975
  have eq154027 : ∀ X0 : G, (M.op (σ x) (σ x)) = X0 ∨ y = (M.op y x) ∨ y = (k (τ X0) x) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq4383 X0
       have i₂ := eq7403 X0
       grind)
    | exact superpose eq7403 eq4383
    | (have j1 := eq7403 X0
       grind)
    | exact resolve eq4383 eq7403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4383 eq7403
  have eq154476 : ∀ X0 : G, (M.op (σ x) (σ x)) = X0 ∨ y = (M.op y x) ∨ y = (k (τ X0) x) := by
    intro X0
    first
    | (have j0 := eq154027 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154027
  have eq227858 : ∀ X0 X1 : G, (M.op X1 (σ x)) = X0 ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ y = (k (τ X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq7113 X1 (σ x)
       have i₂ := eq154476 X0
       grind)
    | (have i₁ := eq7113 X0 X1
       have i₂ := eq154476 (M.op X1 (σ x))
       grind)
    | exact superpose eq154476 eq7113
    | (have j1 := eq154476 X0
       grind)
    | exact resolve eq7113 eq154476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7113
  have eq227954 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 X0) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ y = (k (τ X0) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23526 X0 (σ x) X2
       have i₂ := eq154476 X0
       grind)
    | (have i₁ := eq23526 X0 X1 X2
       have i₂ := eq154476 (M.op X1 X1)
       grind)
    | exact superpose eq154476 eq23526
    | (have j1 := eq154476 X0
       grind)
    | exact resolve eq23526 eq154476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq154476
  have eq228033 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 X0) ∨ y = (M.op y x) ∨ y = (k (τ X0) x) := by
    intro X0 X1 X2
    first
    | (have j0 := eq227954 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227954
  have eq228126 : ∀ X0 X1 : G, y = (k (τ X0) x) ∨ y = (M.op y x) ∨ (M.op X1 (σ x)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq227858 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227858
  have eq237424 : ∀ X0 X1 : G, (σ X0) = (M.op X1 (σ x)) ∨ y = (M.op y x) ∨ y = (k X0 x) := by
    intro X0 X1
    first
    | (have i₁ := eq228126 (σ X0) X1
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq228126
    | (have j0 := eq228126 (σ X0) X1
       grind)
    | exact resolve eq228126 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228126
  have eq241082 : ∀ X0 X1 : G, (τ (M.op X0 (σ x))) = X1 ∨ y = (M.op y x) ∨ y = (k X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1
       have i₂ := eq237424 X1 X0
       grind)
    | exact superpose eq237424 eq9
    | (have j1 := eq237424 X1 X1
       grind)
    | exact resolve eq9 eq237424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237424
  have eq275406 : ∀ X0 : G, (σ x) ≠ (σ (M.op X0 y)) ∨ y = (M.op y x) ∨ y = (M.op y x) ∨ y = (k (τ y) x) := by
    intro X0
    first
    | (have i₁ := eq3221
       have i₂ := eq228033 y x X0
       grind)
    | (have i₁ := eq3221
       have i₂ := eq228033 y X0 x
       grind)
    | exact superpose eq228033 eq3221
    | (have j1 := eq228033 y x x
       grind)
    | exact resolve eq3221 eq228033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3221 eq228033
  have eq275427 : ∀ X0 : G, (σ x) ≠ (σ (M.op X0 y)) ∨ y = (M.op y x) ∨ y = (k (τ y) x) := by
    intro X0
    first
    | (have j0 := eq275406 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275406
  have eq452337 : ∀ X0 : G, (τ (σ y)) ≠ (τ (M.op (σ y) (σ y))) ∨ (k X0 (τ (σ y))) = (M.op X0 (τ (σ y))) ∨ x = (k y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq1219 (σ y) X0
       have i₂ := eq88529 (σ y)
       grind)
    | exact superpose eq88529 eq1219
    | (have j0 := eq1219 (σ y) X0
       grind)
    | exact resolve eq1219 eq88529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219
  have eq452340 : (τ (σ y)) ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq1213 (σ y)
       have i₂ := eq88529 (σ y)
       grind)
    | exact superpose eq88529 eq1213
    | (have j0 := eq1213 (σ y)
       grind)
    | exact resolve eq1213 eq88529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1213 eq88529
  have eq452763 : y ≠ (τ (M.op (σ y) (σ y))) ∨ (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq452340
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq452340
    | exact resolve eq452340 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452340
  have eq452764 : ∀ X0 : G, y ≠ (τ (M.op (σ y) (σ y))) ∨ (k X0 (τ (σ y))) = (M.op X0 (τ (σ y))) ∨ x = (k y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq452337 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq452337
    | (have j0 := eq452337 X0
       grind)
    | exact resolve eq452337 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452337
  have eq452769 : (τ (σ y)) = (M.op (τ (σ y)) (τ (σ y))) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | (have j1 := eq130598 x y
       grind)
    | (have r₁ := eq452763
       have r₂ := eq130598 (σ y) y
       grind)
    | exact resolve eq452763 eq130598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452763
  have eq452770 : ∀ X0 : G, (k X0 (τ (σ y))) = (M.op X0 (τ (σ y))) ∨ x = (k y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq452764 X0
       have j1 := eq130598 X0 y
       grind)
    | (have r₁ := eq452764 X0
       have r₂ := eq130598 (σ y) y
       grind)
    | exact resolve eq452764 eq130598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130598 eq452764
  have eq452771 : y = (M.op y y) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq452769
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq452769
    | exact resolve eq452769 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452769
  have eq452772 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (k y y) ∨ y = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq452770 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq452770
    | exact resolve eq452770 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452770
  have eq457970 : x ≠ (M.op y y) ∨ x = (k y y) ∨ y = (M.op y x) := by grind
  clear eq452772
  have eq458673 : x ≠ y ∨ x = (k y y) ∨ y = (M.op y x) ∨ x = (k y y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq457970
       have i₂ := eq452771
       grind)
    | exact superpose eq452771 eq457970
    | exact resolve eq457970 eq452771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq452771 eq457970
  have eq458682 : x ≠ y ∨ x = (k y y) ∨ y = (M.op y x) := by grind
  clear eq458673
  have eq458683 : y = (M.op y x) ∨ x = (k y y) := by
    first
    | (have j1 := eq134045 (k y y)
       grind)
    | (have r₁ := eq458682
       have r₂ := eq134045 y
       grind)
    | exact resolve eq458682 eq134045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134045 eq458682
  have eq459348 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op y y)) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq13 y X0 x
       have i₂ := eq458683
       grind)
    | exact superpose eq458683 eq13
    | exact resolve eq13 eq458683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq460263 : ∀ X0 X1 : G, (M.op y (M.op (M.op X0 X1) X0)) = X0 ∨ x = (k y y) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op y y) X1
       have i₂ := eq459348 y
       grind)
    | exact superpose eq459348 eq13
    | exact resolve eq13 eq459348
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq459348
  have eq462859 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op y X0) ∨ x = (k y y) := by
    intro X0 X1
    first
    | (have i₁ := eq460263 (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)
       have i₂ := eq13 X0 (M.op (M.op X0 X1) X0) X1
       grind)
    | exact superpose eq13 eq460263
    | exact resolve eq460263 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465451 : ∀ X0 : G, (M.op y (M.op y X0)) = X0 ∨ x = (k y y) ∨ x = (k y y) := by
    intro X0
    first
    | (have i₁ := eq460263 X0 x
       have i₂ := eq462859 X0 x
       grind)
    | exact superpose eq462859 eq460263
    | exact resolve eq460263 eq462859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460263 eq462859
  have eq465896 : ∀ X0 : G, (M.op y (M.op y X0)) = X0 ∨ x = (k y y) := by
    intro X0
    first
    | (have j0 := eq465451 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465451
  have eq466769 : x = (M.op y y) ∨ x = (k y y) ∨ x = (k y y) := by
    first
    | (have i₁ := eq465896 x
       have i₂ := eq458683
       grind)
    | exact superpose eq458683 eq465896
    | exact resolve eq465896 eq458683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq458683 eq465896
  have eq466914 : x = (k y y) ∨ x = (M.op y y) := by grind
  clear eq466769
  have eq467818 : x = (M.op y y) ∨ y = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq359 y y
       have i₂ := eq466914
       grind)
    | exact superpose eq466914 eq359
    | (have j0 := eq359 y y
       grind)
    | exact resolve eq359 eq466914
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359
  have eq467867 : y = (M.op y y) ∨ x = (M.op y y) := by grind
  clear eq467818
  have eq468789 : ∀ X0 : G, y ≠ y ∨ (k X0 y) = (M.op X0 y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y
       have i₂ := eq467867
       grind)
    | exact superpose eq467867 eq16
    | (have j0 := eq16 X0 y
       grind)
    | (have r₁ := eq16 X0 y
       have r₂ := eq467867
       grind)
    | exact resolve eq16 eq467867
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467867
  have eq468925 : ∀ X0 : G, (k X0 y) = (M.op X0 y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have j0 := eq468789 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468789
  have eq475142 : x = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq466914
       have i₂ := eq468925 y
       grind)
    | exact superpose eq468925 eq466914
    | exact resolve eq466914 eq468925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466914 eq468925
  have eq475147 : x = (M.op y y) := by grind
  clear eq475142
  have eq476586 : (σ x) ≠ (σ x) ∨ y = (M.op y x) ∨ y = (k (τ y) x) := by
    first
    | (have i₁ := eq275427 y
       have i₂ := eq475147
       grind)
    | exact superpose eq475147 eq275427
    | exact resolve eq275427 eq475147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq275427
  have eq476590 : ∀ X0 X1 : G, (M.op x (M.op (M.op X0 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 y X1
       have i₂ := eq475147
       grind)
    | exact superpose eq475147 eq13
    | exact resolve eq13 eq475147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476666 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 x) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq23526 X0 y x
       have i₂ := eq475147
       grind)
    | exact superpose eq475147 eq23526
    | exact resolve eq23526 eq475147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23526
  have eq476729 : y = (k (τ y) x) ∨ y = (M.op y x) := by grind
  clear eq476586
  have eq478555 : ∀ X0 : G, x = (M.op x (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq476590 x (M.op (M.op X0 x) X0)
       have i₂ := eq476590 X0 x
       grind)
    | exact superpose eq476590 eq476590
    | exact resolve eq476590 eq476590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478568 : y = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq476590 y y
       have i₂ := eq475147
       grind)
    | exact superpose eq475147 eq476590
    | exact resolve eq476590 eq475147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478630 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq476590 (M.op (M.op X0 X1) X0) (M.op (M.op X0 X1) X0)
       have i₂ := eq13 X0 (M.op (M.op X0 X1) X0) X1
       grind)
    | exact superpose eq13 eq476590
    | exact resolve eq476590 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480362 : ∀ X0 : G, x ≠ x ∨ x = (M.op x x) ∨ (M.op x x) = (k (M.op X0 x) x) := by
    intro X0
    first
    | (have i₁ := eq15 (M.op X0 x) x
       have i₂ := eq478555 X0
       grind)
    | exact superpose eq478555 eq15
    | (have j0 := eq15 (M.op X0 x) x
       grind)
    | (have r₁ := eq15 (M.op X0 x) x
       have r₂ := eq478555 X0
       grind)
    | exact resolve eq15 eq478555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480395 : ∀ X0 : G, (M.op x x) = (k (M.op X0 x) x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq480362 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480362
  have eq484455 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x X0) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq478630 (M.op X0 X1) X0
       have i₂ := eq478630 X0 X1
       grind)
    | exact superpose eq478630 eq478630
    | exact resolve eq478630 eq478630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484501 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (M.op x (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq478630 (M.op X1 X1) (M.op (M.op X0 x) X0)
       have i₂ := eq13 X0 X1 x
       grind)
    | exact superpose eq13 eq478630
    | exact resolve eq478630 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484683 : ∀ X0 : G, (M.op x x) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq478630 x (M.op (M.op X0 x) X0)
       have i₂ := eq476590 X0 x
       grind)
    | exact superpose eq476590 eq478630
    | exact resolve eq478630 eq476590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484684 : (M.op y x) = (M.op x x) := by
    first
    | (have i₁ := eq478630 x (M.op x y)
       have i₂ := eq478568
       grind)
    | exact superpose eq478568 eq478630
    | exact resolve eq478630 eq478568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478568
  have eq484890 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op x X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1 x
       have i₂ := eq478630 X0 x
       grind)
    | exact superpose eq478630 eq13
    | exact resolve eq13 eq478630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq484915 : ∀ X0 : G, (M.op x (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq476590 X0 x
       have i₂ := eq478630 X0 x
       grind)
    | exact superpose eq478630 eq476590
    | exact resolve eq476590 eq478630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476590
  have eq486686 : ∀ X0 X1 : G, (M.op X0 x) = (M.op X1 x) := by
    intro X0 X1
    first
    | (have i₁ := eq484683 X1
       have i₂ := eq484683 X0
       grind)
    | (have i₁ := eq484683 X0
       have i₂ := eq484683 x
       grind)
    | exact superpose eq484683 eq484683
    | exact resolve eq484683 eq484683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486774 : ∀ X0 X1 X2 : G, (M.op (M.op X0 x) (M.op (M.op X1 X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 x X2
       have i₂ := eq484683 X0
       grind)
    | (have i₁ := eq13 X0 x X2
       have i₂ := eq484683 x
       grind)
    | exact superpose eq484683 eq13
    | exact resolve eq13 eq484683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484683
  have eq487223 : ∀ X0 X1 : G, (M.op (M.op X0 x) (M.op x X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq486774 X0 X1 x
       have i₂ := eq478630 X1 x
       grind)
    | exact superpose eq478630 eq486774
    | exact resolve eq486774 eq478630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486774
  have eq495839 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (M.op x X0) X1 (M.op x X0)
       have i₂ := eq484890 X0 (M.op x X0)
       grind)
    | exact superpose eq484890 eq13
    | exact resolve eq13 eq484890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484890
  have eq501010 : ∀ X0 X1 : G, (M.op X0 (M.op X1 x)) = (M.op x (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq478630 (M.op X1 x) (M.op x X0)
       have i₂ := eq487223 X1 X0
       grind)
    | exact superpose eq487223 eq478630
    | exact resolve eq478630 eq487223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq487223
  have eq501011 : ∀ X0 X1 : G, x = (M.op X0 (M.op X1 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq501010 X0 X1
       have i₂ := eq478555 X1
       grind)
    | exact superpose eq478555 eq501010
    | exact resolve eq501010 eq478555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478555 eq501010
  have eq502254 : ∀ X0 X1 : G, x ≠ (M.op X0 x) ∨ (M.op X1 (M.op X0 x)) = (k X1 (M.op X0 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 (M.op X0 x)
       have i₂ := eq501011 (M.op X0 x) X0
       grind)
    | exact superpose eq501011 eq16
    | (have j0 := eq16 X1 (M.op X0 x)
       grind)
    | exact resolve eq16 eq501011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq502711 : ∀ X0 X1 : G, x ≠ (M.op X0 x) ∨ x = (k X1 (M.op X0 x)) := by
    intro X0 X1
    first
    | (have i₁ := eq502254 X0 X1
       have i₂ := eq501011 X1 X0
       grind)
    | exact superpose eq501011 eq502254
    | (have j0 := eq502254 X0 X1
       grind)
    | exact resolve eq502254 eq501011
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502254
  have eq514438 : (σ y) = (k y (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq18 y x
       have i₂ := eq476729
       grind)
    | exact superpose eq476729 eq18
    | exact resolve eq18 eq476729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq476729
  have eq514909 : (σ y) = (k y (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq514438
       have i₂ := eq484684
       grind)
    | exact superpose eq484684 eq514438
    | exact resolve eq514438 eq484684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq514438
  have eq521478 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq484501 X0 X1
       have i₂ := eq484501 X2 X1
       grind)
    | (have i₁ := eq484501 X0 X1
       have i₂ := eq484501 x X1
       grind)
    | exact superpose eq484501 eq484501
    | exact resolve eq484501 eq484501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484501
  have eq532154 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) X2) = (M.op x X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq478630 X2 (M.op X1 X1)
       have i₂ := eq521478 X2 X1 X0
       grind)
    | (have i₁ := eq478630 X2 (M.op X1 X1)
       have i₂ := eq521478 X0 X1 X2
       grind)
    | exact superpose eq521478 eq478630
    | exact resolve eq478630 eq521478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521478
  have eq560519 : ∀ X0 : G, y ≠ (M.op X0 x) ∨ y = (M.op y x) := by
    intro X0
    grind
  clear eq476666
  have eq561248 : ∀ X0 : G, y ≠ (M.op X0 x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq560519 X0
       have i₂ := eq484684
       grind)
    | exact superpose eq484684 eq560519
    | (have j0 := eq560519 X0
       grind)
    | exact resolve eq560519 eq484684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560519
  have eq577868 : (τ (σ y)) = (k (τ y) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq28 y x
       have i₂ := eq514909
       grind)
    | exact superpose eq514909 eq28
    | exact resolve eq28 eq514909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq514909
  have eq577966 : y = (k (τ y) x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq577868
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq577868
    | exact resolve eq577868 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577868
  have eq618206 : ∀ X0 X1 : G, (M.op x X0) = (M.op (σ y) (M.op (M.op x (M.op X0 X1)) (M.op x X0))) ∨ y = (M.op y x) := by
    intro X0 X1
    first
    | (have i₁ := eq2631 (M.op x X0) (M.op X0 X1)
       have i₂ := eq484455 X0 X1
       grind)
    | exact superpose eq484455 eq2631
    | exact resolve eq2631 eq484455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2631
  have eq618238 : ∀ X0 X1 : G, (M.op x (M.op x X0)) = (M.op (M.op x (M.op X0 X1)) (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq478630 (M.op x X0) (M.op X0 X1)
       have i₂ := eq484455 X0 X1
       grind)
    | exact superpose eq484455 eq478630
    | exact resolve eq478630 eq484455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484455
  have eq618239 : ∀ X0 X1 : G, (M.op (M.op x (M.op X0 X1)) (M.op x X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq618238 X0 X1
       have i₂ := eq484915 X0
       grind)
    | exact superpose eq484915 eq618238
    | exact resolve eq618238 eq484915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618238
  have eq618260 : ∀ X0 X1 : G, y = (M.op x x) ∨ (M.op x X0) = (M.op (σ y) (M.op (M.op x (M.op X0 X1)) (M.op x X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq618206 X0 X1
       have i₂ := eq484684
       grind)
    | exact superpose eq484684 eq618206
    | (have j0 := eq618206 X0 X1
       grind)
    | exact resolve eq618206 eq484684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484684 eq618206
  have eq618385 : ∀ X0 : G, (M.op (σ y) X0) = (M.op x X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq618260 X0 x
       have i₂ := eq618239 X0 x
       grind)
    | exact superpose eq618239 eq618260
    | exact resolve eq618260 eq618239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618260
  have eq620348 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op x (M.op (M.op x X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq618239 (M.op x X0) X1
       have i₂ := eq484915 X0
       grind)
    | exact superpose eq484915 eq618239
    | exact resolve eq618239 eq484915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639926 : ∀ X0 : G, (σ y) = (M.op (M.op x (M.op X0 X0)) (σ x)) ∨ y = (M.op y x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq5962 X0
       have i₂ := eq618385 (M.op X0 X0)
       grind)
    | exact superpose eq618385 eq5962
    | exact resolve eq5962 eq618385
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5962 eq618385
  have eq640620 : ∀ X0 : G, (σ y) = (M.op (M.op x (M.op X0 X0)) (σ x)) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq639926 X0
       grind)
    | (have r₁ := eq639926 X0
       have r₂ := eq561248 y
       grind)
    | (have r₁ := eq639926 X0
       have r₂ := eq561248 x
       grind)
    | exact resolve eq639926 eq561248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639926
  have eq640747 : (σ y) = (M.op x (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq640620 x
       have i₂ := eq532154 x x (σ x)
       grind)
    | exact superpose eq532154 eq640620
    | exact resolve eq640620 eq532154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq532154 eq640620
  have eq641983 : ∀ X0 : G, (τ (σ y)) = X0 ∨ y = (M.op y x) ∨ y = (k X0 x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq241082 x X0
       have i₂ := eq640747
       grind)
    | exact superpose eq640747 eq241082
    | (have j0 := eq241082 X0 X0
       grind)
    | exact resolve eq241082 eq640747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241082 eq640747
  have eq642056 : ∀ X0 : G, (τ (σ y)) = X0 ∨ y = (k X0 x) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq641983 X0
       grind)
    | (have r₁ := eq641983 X0
       have r₂ := eq561248 y
       grind)
    | (have r₁ := eq641983 X0
       have r₂ := eq561248 x
       grind)
    | exact resolve eq641983 eq561248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq641983
  have eq642113 : ∀ X0 : G, y = (k X0 x) ∨ y = X0 ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq642056 X0
       have i₂ := eq9 y
       grind)
    | exact superpose eq9 eq642056
    | (have j0 := eq642056 X0
       grind)
    | exact resolve eq642056 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642056
  have eq722157 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op X0 x) ∨ y = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq642113 (M.op X0 x)
       have i₂ := eq480395 X0
       grind)
    | exact superpose eq480395 eq642113
    | (have j0 := eq642113 (M.op x x)
       grind)
    | exact resolve eq642113 eq480395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480395 eq642113
  have eq722211 : ∀ X0 : G, y = (M.op x x) ∨ y = (M.op X0 x) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq722157 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722157
  have eq722216 : y = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq722211 x
       grind)
    | (have r₁ := eq722211 x
       have r₂ := eq561248 x
       grind)
    | (have r₁ := eq722211 x
       have r₂ := eq561248 x
       grind)
    | exact resolve eq722211 eq561248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722211
  have eq723419 : ∀ X0 : G, y = (M.op X0 x) ∨ x = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq722216
       have i₂ := eq486686 x x
       grind)
    | (have i₁ := eq722216
       have i₂ := eq486686 X0 x
       grind)
    | exact superpose eq486686 eq722216
    | exact resolve eq722216 eq486686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq723461 : ∀ X0 : G, x = (M.op x x) ∨ x = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq501011 X0 x
       have i₂ := eq722216
       grind)
    | exact superpose eq722216 eq501011
    | exact resolve eq501011 eq722216
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq722216
  have eq731134 : ∀ X0 X1 : G, x = (M.op X1 x) ∨ x = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq501011 X0 X1
       have i₂ := eq723419 X1
       grind)
    | exact superpose eq723419 eq501011
    | (have j1 := eq723419 X1
       grind)
    | exact resolve eq501011 eq723419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723419
  have eq736237 : ∀ X0 X1 : G, x ≠ x ∨ x = (k X0 x) ∨ x = (M.op X1 y) := by
    intro X0 X1
    first
    | (have i₁ := eq502711 x X1
       have i₂ := eq723461 X0
       grind)
    | exact superpose eq723461 eq502711
    | (have j1 := eq723461 X1
       grind)
    | (have r₁ := eq502711 x X1
       have r₂ := eq723461 X0
       grind)
    | exact resolve eq502711 eq723461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723461
  have eq736412 : ∀ X0 X1 : G, x = (k X0 x) ∨ x = (M.op X1 y) := by
    intro X0 X1
    first
    | (have j0 := eq736237 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736237
  have eq740342 : ∀ X1 : G, x ≠ y ∨ y = (M.op x x) ∨ x = (M.op X1 y) := by
    intro X1
    first
    | (have i₁ := eq561248 x
       have i₂ := eq731134 X1 x
       grind)
    | exact superpose eq731134 eq561248
    | (have j1 := eq731134 X1 X1
       grind)
    | exact resolve eq561248 eq731134
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561248 eq731134
  have eq743739 : ∀ X0 : G, x = y ∨ y = (M.op x x) ∨ x = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq577966
       have i₂ := eq736412 (τ y) X0
       grind)
    | exact superpose eq736412 eq577966
    | (have j1 := eq736412 X0 X0
       grind)
    | exact resolve eq577966 eq736412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577966 eq736412
  have eq743961 : ∀ X0 : G, y = (M.op x x) ∨ x = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq743739 X0
       have j1 := eq740342 X0
       grind)
    | (have r₁ := eq743739 X0
       have r₂ := eq740342 x
       grind)
    | exact resolve eq743739 eq740342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740342 eq743739
  have eq745495 : ∀ X0 X1 : G, x = (M.op X1 y) ∨ x = (M.op X0 y) := by
    intro X0 X1
    first
    | (have i₁ := eq501011 X1 x
       have i₂ := eq743961 X0
       grind)
    | exact superpose eq743961 eq501011
    | (have j1 := eq743961 X1
       grind)
    | exact resolve eq501011 eq743961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq501011 eq743961
  have eq748423 : ∀ X0 : G, x ≠ x ∨ x = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq745495 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745495
  have eq748424 : ∀ X0 : G, x = (M.op X0 y) := by
    intro X0
    first
    | (have j0 := eq748423 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748423
  have eq750758 : y = (M.op x x) := by
    first
    | (have i₁ := eq484915 y
       have i₂ := eq748424 x
       grind)
    | exact superpose eq748424 eq484915
    | exact resolve eq484915 eq748424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq752719 : ∀ X0 : G, y = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq486686 X0 x
       have i₂ := eq750758
       grind)
    | exact superpose eq750758 eq486686
    | exact resolve eq486686 eq750758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486686
  have eq752728 : ∀ X0 : G, x ≠ y ∨ x = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq502711 x x
       have i₂ := eq750758
       grind)
    | exact superpose eq750758 eq502711
    | exact resolve eq502711 eq750758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502711
  have eq752856 : ∀ X0 : G, (M.op y X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq495839 X0 x
       have i₂ := eq750758
       grind)
    | exact superpose eq750758 eq495839
    | exact resolve eq495839 eq750758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq750758
  have eq757267 : ∀ X0 : G, y ≠ (M.op x X0) ∨ y = (M.op y y) ∨ (M.op y y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq15 X0 y
       have i₂ := eq752856 X0
       grind)
    | exact superpose eq752856 eq15
    | (have j0 := eq15 X0 y
       grind)
    | exact resolve eq15 eq752856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752856
  have eq757676 : ∀ X0 : G, x = y ∨ y ≠ (M.op x X0) ∨ (M.op y y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq757267 X0
       have i₂ := eq475147
       grind)
    | exact superpose eq475147 eq757267
    | (have j0 := eq757267 X0
       grind)
    | exact resolve eq757267 eq475147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq757267
  have eq757697 : ∀ X0 : G, x = (k X0 y) ∨ x = y ∨ y ≠ (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq757676 X0
       have i₂ := eq475147
       grind)
    | exact superpose eq475147 eq757676
    | (have j0 := eq757676 X0
       grind)
    | exact resolve eq757676 eq475147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475147 eq757676
  have eq757705 : ∀ X0 : G, y ≠ (M.op x X0) ∨ x = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq757697 X0
       have j1 := eq752728 X0
       grind)
    | (have r₁ := eq757697 X0
       have r₂ := eq752728 X0
       grind)
    | exact resolve eq757697 eq752728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752728 eq757697
  have eq761699 : y ≠ y ∨ x = (k x y) := by
    first
    | (have i₁ := eq757705 x
       have i₂ := eq752719 x
       grind)
    | exact superpose eq752719 eq757705
    | (have j0 := eq757705 x
       grind)
    | (have r₁ := eq757705 x
       have r₂ := eq752719 x
       grind)
    | exact resolve eq757705 eq752719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq752719 eq757705
  have eq761707 : x = (k x y) := by grind
  clear eq761699
  have eq763333 : (σ (M.op x y)) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2308
       have i₂ := eq761707
       grind)
    | exact superpose eq761707 eq2308
    | exact resolve eq2308 eq761707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2308 eq761707
  have eq763371 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq763333
       have i₂ := eq748424 x
       grind)
    | exact superpose eq748424 eq763333
    | exact resolve eq763333 eq748424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763333
  have eq763372 : (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq763371
  have eq764628 : (M.op (σ y) (σ y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq478630 (σ y) (σ x)
       have i₂ := eq763372
       grind)
    | exact superpose eq763372 eq478630
    | exact resolve eq478630 eq763372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478630
  have eq767701 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x (σ y)) X0) := by
    intro X0
    first
    | (have i₁ := eq495839 X0 (σ y)
       have i₂ := eq764628
       grind)
    | exact superpose eq764628 eq495839
    | exact resolve eq495839 eq764628
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495839 eq764628
  have eq771426 : ∀ X0 : G, (M.op x (σ y)) = (M.op (M.op x (M.op x X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq620348 (σ y) X0
       have i₂ := eq767701 X0
       grind)
    | exact superpose eq767701 eq620348
    | exact resolve eq620348 eq767701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq767701
  have eq772012 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op x (σ y)) := by
    intro X0
    first
    | (have i₁ := eq771426 X0
       have i₂ := eq484915 X0
       grind)
    | exact superpose eq484915 eq771426
    | exact resolve eq771426 eq484915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq771426
  have eq773848 : ∀ X0 X1 : G, (M.op X0 (σ y)) = (M.op X1 (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq772012 X0
       have i₂ := eq772012 X1
       grind)
    | (have i₁ := eq772012 X0
       have i₂ := eq772012 x
       grind)
    | exact superpose eq772012 eq772012
    | exact resolve eq772012 eq772012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774282 : (σ (M.op x y)) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq11
       have i₂ := eq772012 (σ x)
       grind)
    | exact superpose eq772012 eq11
    | exact resolve eq11 eq772012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774456 : ∀ X0 : G, (σ y) = (M.op x (M.op X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq484915 (σ y)
       have i₂ := eq772012 X0
       grind)
    | (have i₁ := eq484915 (σ y)
       have i₂ := eq772012 x
       grind)
    | exact superpose eq772012 eq484915
    | exact resolve eq484915 eq772012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484915
  have eq774687 : (σ x) ≠ (M.op x (σ y)) := by
    first
    | (have i₁ := eq774282
       have i₂ := eq748424 x
       grind)
    | exact superpose eq748424 eq774282
    | exact resolve eq774282 eq748424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748424 eq774282
  have eq776487 : ∀ X0 : G, (σ x) ≠ (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq774687
       have i₂ := eq772012 X0
       grind)
    | (have i₁ := eq774687
       have i₂ := eq772012 x
       grind)
    | exact superpose eq772012 eq774687
    | exact resolve eq774687 eq772012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772012 eq774687
  have eq780889 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op x (M.op X0 (σ y))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq620348 X1 (σ y)
       have i₂ := eq773848 (M.op x X1) X0
       grind)
    | (have i₁ := eq620348 X1 (σ y)
       have i₂ := eq773848 X0 (M.op x X1)
       grind)
    | exact superpose eq773848 eq620348
    | exact resolve eq620348 eq773848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq620348 eq773848
  have eq781171 : ∀ X1 : G, (M.op (σ y) X1) = (M.op x X1) := by
    intro X1
    first
    | (have i₁ := eq780889 x X1
       have i₂ := eq774456 x
       grind)
    | exact superpose eq774456 eq780889
    | exact resolve eq780889 eq774456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774456 eq780889
  have eq783299 : (σ y) = (M.op x (σ x)) := by
    first
    | (have i₁ := eq763372
       have i₂ := eq781171 (σ x)
       grind)
    | exact superpose eq781171 eq763372
    | exact resolve eq763372 eq781171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763372 eq781171
  have eq785088 : ∀ X0 : G, (σ x) = (M.op (M.op x (M.op (σ x) X0)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq618239 (σ x) X0
       have i₂ := eq783299
       grind)
    | exact superpose eq783299 eq618239
    | exact resolve eq618239 eq783299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618239 eq783299
  have eq785208 : False := by grind
  exact eq785208
