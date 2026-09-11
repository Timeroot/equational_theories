import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_pyy_pyx_pxy_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X0) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq23 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq42 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq42 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq42 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq42 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq56 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 X0 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq56
    | (have j0 := eq56 (σ X0) (σ X1)
       grind)
    | exact resolve eq56 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq43 (τ X0)
       grind)
    | exact superpose eq43 eq18
    | exact resolve eq18 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq83 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq82 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq82
    | exact resolve eq82 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq91 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq83 X0
       have i₂ := eq43 X0
       grind)
    | exact superpose eq43 eq83
    | exact resolve eq83 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq83
  have eq95 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq91 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq91
    | exact resolve eq91 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq154 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq25 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq25 eq25
    | exact resolve eq25 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25
  have eq173 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq67 y x
       grind)
    | exact superpose eq67 eq16
    | (have j1 := eq67 y x
       grind)
    | exact resolve eq16 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq189 : ∀ X0 X1 : G, (M.op (M.op (σ (M.op X0 X0)) X1) (M.op (σ X0) X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq95 X0
       grind)
    | exact superpose eq95 eq9
    | exact resolve eq9 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X1) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 X1 (M.op (σ (M.op x x)) X0) (M.op (σ x) X0) X2
       have i₂ := eq189 x X0
       grind)
    | exact superpose eq189 eq23
    | exact resolve eq23 eq189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq189
  have eq446 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq372 (M.op X1 x) X0 (M.op X1 X0)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq372
    | exact resolve eq372 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq574 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X1 (M.op X0 X1)
       have i₂ := eq446 X1 X0
       grind)
    | exact superpose eq446 eq9
    | exact resolve eq9 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq592 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq173
       have i₂ := eq95 y
       grind)
    | exact superpose eq95 eq173
    | exact resolve eq173 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq173
  have eq593 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq592
       have i₂ := eq95 x
       grind)
    | exact superpose eq95 eq592
    | exact resolve eq592 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq638 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq593
       have i₂ := eq56 y x
       grind)
    | exact superpose eq56 eq593
    | (have j1 := eq56 x y
       grind)
    | exact resolve eq593 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq593
  have eq639 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq638
  have eq1752 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq154 X0 X1 (M.op X0 X0)
       have i₂ := eq24 X0 X0 X1
       grind)
    | exact superpose eq24 eq154
    | exact resolve eq154 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq154
  have eq1804 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1752 X0 X1
       have i₂ := eq574 X0 X0
       grind)
    | exact superpose eq574 eq1752
    | exact resolve eq1752 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1752
  have eq11536 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq639
       grind)
    | exact superpose eq639 eq10
    | exact resolve eq10 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq11579 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq11536
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq11536
    | exact resolve eq11536 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11536
  have eq11580 : (M.op y y) = (M.op x x) := by grind
  clear eq11579
  have eq11694 : y = (M.op (M.op x x) (M.op x x)) := by
    first
    | (have i₁ := eq1804 y y
       have i₂ := eq11580
       grind)
    | exact superpose eq11580 eq1804
    | exact resolve eq1804 eq11580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1804 eq11580
  have eq11704 : x = y := by
    first
    | (have i₁ := eq11694
       have i₂ := eq574 x x
       grind)
    | exact superpose eq574 eq11694
    | exact resolve eq11694 eq574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574 eq11694
  have eq11756 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11704
       grind)
    | exact superpose eq11704 eq16
    | exact resolve eq16 eq11704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11704
  have eq11757 : False := by grind
  exact eq11757

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_x_pxx_x_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = X0 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  have eq50 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x X0)) = X0 := by
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
  have eq51 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
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
  have eq55 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq84 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 : G, (σ (k x X0)) = (M.op (σ X0) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq35 eq11
    | (have j0 := eq11 (σ x) (σ x)
       grind)
    | exact resolve eq11 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq92 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq36 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq96 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq43
       have i₂ := eq11 x x
       grind)
    | exact superpose eq11 eq43
    | (have j1 := eq11 x x
       grind)
    | exact resolve eq43 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq72
    | (have j1 := eq11 y y
       grind)
    | exact resolve eq72 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq99 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
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
  have eq106 : (k (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq99
  have eq107 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq96
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq97
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq97
    | exact resolve eq97 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq97
  have eq109 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq108
    | exact resolve eq108 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq207 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op x y) X0) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq211 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq51
    | (have j0 := eq51 (σ y)
       grind)
    | exact resolve eq51 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq214 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq223 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op x X0) y) X1) (M.op x y)) y) := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq227 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq228 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq378 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X1) X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (M.op x X0) (M.op (M.op (M.op x x) x) X0) X2
       have i₂ := eq52 x x x X0
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq393 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X1 X0) (M.op X1 x) X0 X2
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq397 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op y X0)) = X0 := by
    intro X0
    first
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq400 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1 x (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq402 : (M.op x y) = (M.op (M.op y (M.op x y)) y) := by
    first
    | exact superpose eq54 eq52
    | exact resolve eq52 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq403 : (M.op (σ x) (σ y)) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq55 eq52
    | exact resolve eq52 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : y = (M.op (M.op x y) (M.op y y)) := by
    first
    | exact superpose eq402 eq14
    | exact resolve eq14 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq414 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq403 eq14
    | exact resolve eq14 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq425 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0)
       have i₂ := eq52 X1 x x X0
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq437 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op (M.op x y) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq223 eq53
    | exact resolve eq53 eq223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223
  have eq441 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq227 eq53
    | exact resolve eq53 eq227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227
  have eq443 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op X2 X3) X1) X0) (M.op (M.op (M.op X1 X0) X4) X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op (M.op X1 X2) X0) X3) (M.op X0 X3) X2
       have i₂ := eq52 X0 X1 X2 X3
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq444 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X0) (M.op (M.op (M.op (M.op X1 X2) X0) X3) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 (M.op X1 X0) (M.op (M.op X1 X2) X0) X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq449 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op (M.op x X0) y) X1) y)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq452 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq473 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq55 (M.op (M.op x x) (M.op x sF2))
       have i₂ := eq53 sF2 x x
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq509 : ∀ X0 X1 X2 X4 : G, (M.op X1 X2) = (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X4) (M.op X1 X2)) X2) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq56 X2 X1 (M.op (M.op X0 x) (M.op X0 X1)) X4
       have i₂ := eq53 X1 X0 x
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq511 : ∀ X0 X1 X2 X5 : G, (M.op (M.op X1 X0) X2) = (M.op (M.op (M.op (M.op X0 X2) X5) (M.op (M.op X1 X0) X2)) X2) := by
    intro X0 X1 X2 X5
    first
    | (have i₁ := eq56 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0) X5
       have i₂ := eq52 X1 x x X0
       grind)
    | exact superpose eq52 eq56
    | exact resolve eq56 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq540 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op (M.op y X1) (M.op (M.op x X0) (M.op x y))) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq550 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X3)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq56 X3 X1 X2 (M.op (M.op X0 x) (M.op X0 (M.op (M.op X1 X2) X3)))
       have i₂ := eq53 (M.op (M.op X1 X2) X3) X0 x
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op (M.op X0 X2) X1) X3) (M.op X0 X1)) X4) X1) X5) (M.op X0 X1)) X1) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq56 X0 (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X2 X3
       have i₂ := eq56 X0 X1 X2 X3
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X4) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 (M.op X1 X0) (M.op (M.op X1 X2) X0) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op x y) X0) X1) (M.op x X0)) X2) X0) (M.op x X0)) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq50 eq56
    | exact resolve eq56 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq559 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op (M.op y (M.op x y)) X0) y) X1) (M.op x y)) y) := by
    intro X0 X1
    first
    | exact superpose eq402 eq56
    | exact resolve eq56 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq561 : ∀ X0 X1 X2 : G, y = (M.op (M.op (M.op (M.op (M.op (M.op (M.op x X0) y) X1) (M.op x y)) X2) y) (M.op x y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq54 eq56
    | exact resolve eq56 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq562 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (M.op (M.op (σ y) (M.op (σ x) (σ y))) X0) (σ y)) X1) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq403 eq56
    | exact resolve eq56 eq403
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq563 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X0) (M.op (σ x) (σ y))) X1) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq211 eq56
    | exact resolve eq56 eq211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq211
  have eq573 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq56 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq969 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op (M.op (M.op x y) (M.op (M.op x y) X0)) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq50 eq207
    | exact resolve eq207 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1013 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op x y) X1) X0) (M.op (M.op (M.op X1 X0) X2) X0)) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq207 eq53
    | exact resolve eq53 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq1091 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (M.op (M.op x y) X0)) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq397 eq214
    | exact resolve eq214 eq397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214 eq397
  have eq1525 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq393 X0 (M.op X1 x) (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq393
    | exact resolve eq393 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq1737 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X0 X1)
       have i₂ := eq400 X1 X0
       grind)
    | exact superpose eq400 eq14
    | exact resolve eq14 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2681 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y (M.op (M.op x X0) y)) y)) := by
    intro X0
    first
    | exact superpose eq437 eq449
    | exact resolve eq449 eq437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq437 eq449
  have eq2709 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op x X0) y)) := by
    intro X0
    first
    | (have i₁ := eq2681 X0
       have i₂ := eq400 y (M.op x X0)
       grind)
    | exact superpose eq400 eq2681
    | exact resolve eq2681 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2681
  have eq2763 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (M.op (σ x) X0) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq441 eq452
    | exact resolve eq452 eq441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441 eq452
  have eq2789 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq2763 X0
       have i₂ := eq400 sF3 (M.op sF2 X0)
       grind)
    | exact superpose eq400 eq2763
    | exact resolve eq2763 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2763
  have eq5304 : (M.op y y) = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq2709 eq425
    | exact resolve eq425 eq2709
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2709
  have eq5309 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq2789 eq425
    | exact resolve eq425 eq2789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2789
  have eq5780 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (M.op (M.op (σ y) X1) (M.op (σ x) (σ y)))) := by
    intro X0 X1
    first
    | exact superpose eq473 eq444
    | exact resolve eq444 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq444 eq473
  have eq6216 : ∀ X0 X1 X3 : G, (M.op X0 X3) = (M.op (M.op (M.op X1 X0) (M.op X0 X3)) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq573 (M.op X1 x) (M.op (M.op X0 X1) x) x
       have i₂ := eq378 X0 X1 x
       grind)
    | exact superpose eq378 eq573
    | exact resolve eq573 eq378
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq378
  have eq6358 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq573 X0 X1 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X1
       grind)
    | exact superpose eq53 eq573
    | exact resolve eq573 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq6361 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X1 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq573 (M.op X1 X0) X1 X0
       have i₂ := eq52 X1 X1 X0 X0
       grind)
    | exact superpose eq52 eq573
    | exact resolve eq573 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq573
  have eq6475 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6358 X0 X1
       have i₂ := eq1737 X0 X0
       grind)
    | exact superpose eq1737 eq6358
    | exact resolve eq6358 eq1737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1737 eq6358
  have eq6557 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq26 eq6475
    | (have j0 := eq6475 (σ x) (σ y)
       grind)
    | exact resolve eq6475 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6602 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x X0) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq224 X0 (M.op (M.op x X0) (M.op x X0))
       have i₂ := eq6475 (M.op x X0) y
       grind)
    | exact superpose eq6475 eq224
    | exact resolve eq224 eq6475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq6604 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq228 X0 (M.op (M.op sF2 X0) (M.op sF2 X0))
       have i₂ := eq6475 (M.op sF2 X0) sF3
       grind)
    | exact superpose eq6475 eq228
    | exact resolve eq228 eq6475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228 eq6475
  have eq7217 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 x) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq6602 (M.op x (M.op X0 x))
       have i₂ := eq1525 x X0
       grind)
    | exact superpose eq1525 eq6602
    | exact resolve eq6602 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6602
  have eq7556 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq6604 (M.op sF2 (M.op x sF2))
       have i₂ := eq1525 sF2 x
       grind)
    | exact superpose eq1525 eq6604
    | exact resolve eq6604 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525 eq6604
  have eq8541 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 (M.op (M.op X0 X0) X1) x X0
       have i₂ := eq443 X0 X0 (M.op (M.op X0 X0) X1) x X1
       grind)
    | exact superpose eq443 eq56
    | exact resolve eq56 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq443
  have eq12138 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (M.op (M.op X0 x) (M.op x y)) X1) y) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq561 sF0 (M.op (M.op X1 x) sF0) x
       have i₂ := eq511 x X1 sF0 y
       grind)
    | exact superpose eq511 eq561
    | exact resolve eq561 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq13591 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (M.op (M.op x y) X1)) X1) (M.op x X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq555 x x (M.op (M.op X1 (M.op sF0 x)) x)
       have i₂ := eq511 (M.op sF0 x) X1 x (M.op x x)
       grind)
    | exact superpose eq511 eq555
    | exact resolve eq555 eq511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq511 eq555
  have eq15398 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq554 X1 (M.op X0 X2) x x (M.op X0 X1)
       have i₂ := eq550 (M.op (M.op (M.op (M.op X0 X2) x) X1) x) X0 X2 X1
       grind)
    | exact superpose eq550 eq554
    | exact resolve eq554 eq550
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550 eq554
  have eq16133 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq425 (M.op X1 X0) X1 X0
       have i₂ := eq15398 X1 X0 (M.op X1 X0)
       grind)
    | exact superpose eq15398 eq425
    | exact resolve eq425 eq15398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq16219 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq91 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq91
    | (have j0 := eq91 x
       grind)
    | exact resolve eq91 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq16284 : (σ (k x x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq16219
  have eq16287 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16284
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq16284
    | exact resolve eq16284 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16284
  have eq16294 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | (have j1 := eq13 (σ x) (σ x)
       grind)
    | (have r₁ := eq16287
       have r₂ := eq13 x (σ x)
       grind)
    | exact resolve eq16287 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16287
  have eq16299 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq16294 eq49
    | exact resolve eq49 eq16294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq16359 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq92 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq92
    | (have j0 := eq92 y
       grind)
    | exact resolve eq92 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq16418 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq16359
  have eq16420 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16418
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16418
    | exact resolve eq16418 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16418
  have eq16429 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq16420
       have r₂ := eq13 x (σ y)
       grind)
    | exact resolve eq16420 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16420
  have eq16436 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq16429 eq84
    | exact resolve eq84 eq16429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq24199 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq552 X0 X1 x x (M.op X0 X1) (M.op (M.op X0 X1) (M.op X0 X1))
       have i₂ := eq509 (M.op (M.op (M.op X0 x) X1) x) (M.op X0 X1) (M.op X0 X1) X1
       grind)
    | exact superpose eq509 eq552
    | exact resolve eq552 eq509
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509 eq552
  have eq45987 : (M.op (σ y) (σ y)) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq16429 eq106
    | exact resolve eq106 eq16429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq45988 : (M.op (σ x) (σ x)) = (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq16294 eq107
    | exact resolve eq107 eq16294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq63654 : (M.op y y) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq45987
       grind)
    | exact superpose eq45987 eq16
    | exact resolve eq16 eq45987
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45987
  have eq63739 : (k y y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq16436 eq63654
    | exact resolve eq63654 eq16436
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63654
  have eq63742 : (k y y) = (M.op y y) := by
    first
    | (have j1 := eq13 y y
       grind)
    | (have r₁ := eq63739
       have r₂ := eq13 x y
       grind)
    | exact resolve eq63739 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63739
  have eq63743 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq63742
       grind)
    | exact superpose eq63742 eq73
    | exact resolve eq73 eq63742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq63779 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq16429 eq63743
    | exact resolve eq63743 eq16429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16429 eq63743
  have eq63885 : (M.op x x) = (τ (M.op (σ x) (σ x))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq45988
       grind)
    | exact superpose eq45988 eq16
    | exact resolve eq16 eq45988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45988
  have eq63972 : (k x x) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq16299 eq63885
    | exact resolve eq63885 eq16299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63885
  have eq63975 : (k x x) = (M.op x x) := by
    first
    | (have j1 := eq13 x x
       grind)
    | (have r₁ := eq63972
       have r₂ := eq13 x x
       grind)
    | exact resolve eq63972 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63972
  have eq63976 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq63975
       grind)
    | exact superpose eq63975 eq43
    | exact resolve eq43 eq63975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq64012 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | exact superpose eq16294 eq63976
    | exact resolve eq63976 eq16294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16294 eq63976
  have eq71790 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq109 eq11
    | (have j0 := eq11 (σ y) (σ y)
       grind)
    | exact resolve eq11 eq109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq71798 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq71790
    | exact resolve eq71790 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq71790
  have eq71809 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq71798
       have r₂ := eq27
       grind)
    | exact resolve eq71798 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71798
  have eq71822 : (τ (σ y)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq71809 eq16436
    | exact resolve eq16436 eq71809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16436 eq71809
  have eq71968 : (τ (σ y)) = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71822
       have i₂ := eq63742
       grind)
    | exact superpose eq63742 eq71822
    | exact resolve eq71822 eq63742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63742 eq71822
  have eq71979 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq71968
    | exact resolve eq71968 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq71968
  have eq71980 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq71979
  have eq71983 : (τ (σ x)) = (k x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq71980 eq16299
    | exact resolve eq16299 eq71980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16299 eq71980
  have eq72178 : (τ (σ x)) = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71983
       have i₂ := eq63975
       grind)
    | exact superpose eq63975 eq71983
    | exact resolve eq71983 eq63975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63975 eq71983
  have eq72187 : x = (M.op x x) ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq72178
    | exact resolve eq72178 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq72178
  have eq72188 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq72187
  have eq72190 : y = (M.op (M.op x y) y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq408
       have i₂ := eq72188
       grind)
    | exact superpose eq72188 eq408
    | exact resolve eq408 eq72188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408
  have eq72206 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq63779
       have i₂ := eq72188
       grind)
    | exact superpose eq72188 eq63779
    | exact resolve eq63779 eq72188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72338 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72206
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq72206
    | exact resolve eq72206 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72206
  have eq72474 : (M.op y y) = (M.op (M.op y (M.op x y)) y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq72190 eq6361
    | exact resolve eq6361 eq72190
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72190
  have eq72481 : (M.op x y) = (M.op y y) ∨ x = (M.op x x) := by
    first
    | exact superpose eq402 eq72474
    | exact resolve eq72474 eq402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq402 eq72474
  have eq72634 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq72338 eq414
    | exact resolve eq414 eq72338
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414
  have eq72984 : y = (M.op x y) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72188
       have i₂ := eq72481
       grind)
    | exact superpose eq72481 eq72188
    | exact resolve eq72188 eq72481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72188 eq72481
  have eq73099 : x = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq72984
  have eq73123 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq64012
       have i₂ := eq73099
       grind)
    | exact superpose eq73099 eq64012
    | exact resolve eq64012 eq73099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73167 : (M.op x y) = (M.op (M.op x (M.op x y)) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq7217 x
       have i₂ := eq73099
       grind)
    | exact superpose eq73099 eq7217
    | exact resolve eq7217 eq73099
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7217 eq73099
  have eq73281 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5304 eq73167
    | exact resolve eq73167 eq5304
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5304 eq73167
  have eq73306 : (σ x) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq73123
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq73123
    | exact resolve eq73123 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73123
  have eq73478 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq63779
       have i₂ := eq73281
       grind)
    | exact superpose eq73281 eq63779
    | exact resolve eq63779 eq73281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73281
  have eq73603 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq73478
    | exact resolve eq73478 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73478
  have eq73827 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq73306 eq7556
    | exact resolve eq7556 eq73306
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7556 eq73306
  have eq73941 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq5309 eq73827
    | exact resolve eq73827 eq5309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73827
  have eq75230 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq73941 eq73603
    | exact resolve eq73603 eq73941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73603 eq73941
  have eq75346 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq75230
  have eq75350 : y = (M.op x y) := by
    first
    | (have r₁ := eq75346
       have r₂ := eq27
       grind)
    | exact resolve eq75346 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75346
  have eq75362 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq75350 eq20
    | exact resolve eq20 eq75350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq75668 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq75362
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq75362
    | exact resolve eq75362 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75362
  have eq75677 : ∀ X0 X1 : G, y = (M.op (M.op (M.op (M.op (M.op (M.op y y) X0) y) X1) y) y) := by
    intro X0 X1
    first
    | exact superpose eq75350 eq559
    | exact resolve eq559 eq75350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq75678 : ∀ X1 : G, y = (M.op (M.op (M.op (M.op y y) X1) y) y) := by
    intro X1
    first
    | (have i₁ := eq75677 x X1
       have i₂ := eq8541 y x
       grind)
    | exact superpose eq8541 eq75677
    | exact resolve eq75677 eq8541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75677
  have eq75679 : y = (M.op (M.op y y) y) := by
    first
    | (have i₁ := eq75678 x
       have i₂ := eq8541 y x
       grind)
    | exact superpose eq8541 eq75678
    | exact resolve eq75678 eq8541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8541 eq75678
  have eq75788 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq75668 eq5309
    | exact resolve eq5309 eq75668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5309
  have eq76236 : ∀ X0 : G, (M.op y X0) = (M.op (M.op y (M.op y X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq6216 y (M.op y y) X0
       have i₂ := eq75679
       grind)
    | exact superpose eq75679 eq6216
    | exact resolve eq6216 eq75679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6216 eq75679
  have eq76247 : ∀ X0 : G, (M.op X0 X0) = (M.op y X0) := by
    intro X0
    first
    | (have i₁ := eq76236 X0
       have i₂ := eq16133 X0 y
       grind)
    | exact superpose eq16133 eq76236
    | exact resolve eq76236 eq16133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16133 eq76236
  have eq76432 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) X0) (σ (M.op x y))) X1) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq75668 eq562
    | exact resolve eq562 eq75668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq76846 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op y (σ x))) := by
    first
    | (have i₁ := eq6557
       have i₂ := eq76247 sF2
       grind)
    | exact superpose eq76247 eq6557
    | exact resolve eq6557 eq76247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6557
  have eq76907 : (σ y) = (M.op y (σ y)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72338
       have i₂ := eq76247 sF3
       grind)
    | exact superpose eq76247 eq72338
    | exact resolve eq72338 eq76247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72338
  have eq77123 : (σ (M.op x y)) = (M.op y (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq75668 eq76907
    | exact resolve eq76907 eq75668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76907
  have eq77392 : (M.op (σ x) (σ y)) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq13591 eq76432
    | exact resolve eq76432 eq13591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13591 eq76432
  have eq77614 : ∀ X0 X1 : G, (σ (M.op x y)) = (M.op (M.op (M.op (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) X0) (M.op (σ x) (σ y))) X1) (σ (M.op x y))) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq75668 eq563
    | exact resolve eq563 eq75668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq77847 : (σ (M.op x y)) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq77614 eq24199
    | exact resolve eq24199 eq77614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24199 eq77614
  have eq77848 : (σ (M.op x y)) = (M.op (M.op y (σ (M.op x y))) (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq77847
       have i₂ := eq76247 sF1
       grind)
    | exact superpose eq76247 eq77847
    | exact resolve eq77847 eq76247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77847
  have eq81671 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op (M.op y (M.op y X0)) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq75350 eq969
    | exact resolve eq969 eq75350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq969
  have eq82004 : ∀ X0 : G, (M.op (M.op x X0) (M.op x y)) = (M.op (M.op (M.op x y) (M.op (M.op x X0) (M.op x y))) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq540 X0 (M.op (M.op y (M.op y y)) (M.op x y))
       have i₂ := eq81671 y
       grind)
    | exact superpose eq81671 eq540
    | exact resolve eq540 eq81671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq540 eq81671
  have eq82141 : ∀ X0 : G, (M.op (M.op x X0) y) = (M.op (M.op (M.op x y) (M.op (M.op x X0) y)) y) := by
    intro X0
    first
    | exact superpose eq75350 eq82004
    | exact resolve eq82004 eq75350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82004
  have eq82246 : ∀ X0 : G, (M.op (M.op x X0) y) = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq82141 X0
       have i₂ := eq15398 x y X0
       grind)
    | exact superpose eq15398 eq82141
    | exact resolve eq82141 eq15398
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15398 eq82141
  have eq83948 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op y X1) X0) (M.op (M.op (M.op X1 X0) X2) X0)) = X0 := by
    intro X0 X1 X2
    first
    | exact superpose eq75350 eq1013
    | exact resolve eq1013 eq75350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1013
  have eq84785 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op y (M.op (M.op X0 x) (M.op x y))) (M.op x y)) y) := by
    intro X0
    first
    | exact superpose eq12138 eq83948
    | exact resolve eq83948 eq12138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12138 eq83948
  have eq84990 : ∀ X0 : G, y = (M.op (M.op (M.op y (M.op (M.op X0 x) y)) y) y) := by
    intro X0
    first
    | exact superpose eq75350 eq84785
    | exact resolve eq84785 eq75350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84785
  have eq85317 : ∀ X0 : G, y = (M.op (M.op (M.op X0 x) y) y) := by
    intro X0
    first
    | (have i₁ := eq84990 X0
       have i₂ := eq400 y (M.op X0 x)
       grind)
    | exact superpose eq400 eq84990
    | exact resolve eq84990 eq400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400 eq84990
  have eq86708 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) (M.op y X0)) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq75350 eq1091
    | exact resolve eq1091 eq75350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091 eq75350
  have eq87100 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (M.op (M.op y (σ y)) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq86708 eq5780
    | exact resolve eq5780 eq86708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5780 eq86708
  have eq87139 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (M.op (M.op y (σ (M.op x y))) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq75668 eq87100
    | exact resolve eq87100 eq75668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87100
  have eq87279 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq77848 eq87139
    | exact resolve eq87139 eq77848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77848 eq87139
  have eq120884 : (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ (M.op x y))) = (M.op y (σ (M.op x y))) := by
    first
    | (have i₁ := eq75788
       have i₂ := eq76247 sF1
       grind)
    | exact superpose eq76247 eq75788
    | exact resolve eq75788 eq76247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75788
  have eq122223 : (σ (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq75668 eq72634
    | exact resolve eq72634 eq75668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72634
  have eq122567 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ (M.op x y)) (M.op (σ x) (σ y))) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq122223 eq6361
    | exact resolve eq6361 eq122223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6361 eq122223
  have eq122586 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | exact superpose eq77392 eq122567
    | exact resolve eq122567 eq77392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77392 eq122567
  have eq122638 : (M.op (σ x) (σ y)) = (M.op y (σ (M.op x y))) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq122586
       have i₂ := eq76247 sF1
       grind)
    | exact superpose eq76247 eq122586
    | exact resolve eq122586 eq76247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122586
  have eq124385 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq122638 eq77123
    | exact resolve eq77123 eq122638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77123 eq122638
  have eq124531 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) := by grind
  clear eq124385
  have eq124567 : x = (M.op x x) := by
    first
    | (have r₁ := eq124531
       have r₂ := eq27
       grind)
    | exact resolve eq124531 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124531
  have eq124585 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq64012
       have i₂ := eq124567
       grind)
    | exact superpose eq124567 eq64012
    | exact resolve eq64012 eq124567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64012
  have eq124637 : y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq85317 x
       have i₂ := eq124567
       grind)
    | exact superpose eq124567 eq85317
    | exact resolve eq85317 eq124567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85317 eq124567
  have eq124800 : y = (M.op y y) := by
    first
    | (have i₁ := eq124637
       have i₂ := eq82246 y
       grind)
    | exact superpose eq82246 eq124637
    | exact resolve eq124637 eq82246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82246 eq124637
  have eq124852 : (σ x) = (M.op y (σ x)) := by
    first
    | (have i₁ := eq124585
       have i₂ := eq76247 sF2
       grind)
    | exact superpose eq76247 eq124585
    | exact resolve eq124585 eq76247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124585
  have eq124927 : (σ x) = (M.op y (σ x)) := by
    first
    | (have i₁ := eq124852
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq124852
    | exact resolve eq124852 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq124852
  have eq125012 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq63779
       have i₂ := eq124800
       grind)
    | exact superpose eq124800 eq63779
    | exact resolve eq63779 eq124800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63779 eq124800
  have eq125225 : (σ y) = (M.op y (σ y)) := by
    first
    | (have i₁ := eq125012
       have i₂ := eq76247 sF3
       grind)
    | exact superpose eq76247 eq125012
    | exact resolve eq125012 eq76247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76247 eq125012
  have eq125257 : (σ y) = (M.op y (σ (M.op x y))) := by
    first
    | exact superpose eq75668 eq125225
    | exact resolve eq125225 eq75668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125225
  have eq125270 : (σ y) = (M.op y (σ (M.op x y))) := by
    first
    | (have i₁ := eq125257
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq125257
    | exact resolve eq125257 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq125257
  have eq125281 : (σ (M.op x y)) = (M.op y (σ (M.op x y))) := by
    first
    | exact superpose eq75668 eq125270
    | exact resolve eq125270 eq75668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75668 eq125270
  have eq125297 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq124927 eq76846
    | exact resolve eq76846 eq124927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76846 eq124927
  have eq126981 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ (M.op x y))) := by
    first
    | exact superpose eq125297 eq87279
    | exact resolve eq87279 eq125297
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87279 eq125297
  have eq127130 : (M.op (σ x) (σ y)) = (M.op y (σ (M.op x y))) := by
    first
    | exact superpose eq120884 eq126981
    | exact resolve eq126981 eq120884
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120884 eq126981
  have eq127181 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq125281 eq127130
    | exact resolve eq127130 eq125281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125281 eq127130
  have eq127215 : False := by grind
  exact eq127215

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxx_pxy_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  have eq38 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
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
  have eq55 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq75 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq109 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq109 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq109 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq109 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109
  have eq112 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq110 (σ X0)
       grind)
    | exact superpose eq110 eq10
    | exact resolve eq10 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq110 x
       grind)
    | exact superpose eq110 eq43
    | exact resolve eq43 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq114 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq110 y
       grind)
    | exact superpose eq110 eq73
    | exact resolve eq73 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq115 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq110 sF2
       grind)
    | exact superpose eq110 eq49
    | exact resolve eq49 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq116 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq115
       have i₂ := eq110 x
       grind)
    | exact superpose eq110 eq115
    | exact resolve eq115 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq114
       have i₂ := eq110 sF3
       grind)
    | exact superpose eq110 eq114
    | exact resolve eq114 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq118 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq113
       have i₂ := eq110 sF2
       grind)
    | exact superpose eq110 eq113
    | exact resolve eq113 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq119 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq112 X0
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq112
    | exact resolve eq112 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq278 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq281 : ∀ X0 X1 : G, (M.op x y) = (M.op (M.op (M.op (M.op (M.op x X0) y) X1) (M.op x y)) y) := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq284 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq287 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq55 eq14
    | exact resolve eq14 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq383 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq110 (τ X0)
       grind)
    | exact superpose eq110 eq34
    | exact resolve eq34 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq394 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq383 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq383
    | exact resolve eq383 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq383
  have eq396 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq394 X0
       have i₂ := eq110 X0
       grind)
    | exact superpose eq110 eq394
    | exact resolve eq394 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq394
  have eq497 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X1 X0) (M.op X1 x) X0 X2
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq504 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1 x (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq533 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0)
       have i₂ := eq52 X1 x x X0
       grind)
    | exact superpose eq52 eq53
    | exact resolve eq53 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq545 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op (M.op x y) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq278 eq53
    | exact resolve eq53 eq278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq278
  have eq549 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq284 eq53
    | exact resolve eq53 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq557 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op (M.op x X0) y) X1) y)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq560 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq55 eq53
    | exact resolve eq53 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq685 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq56 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq807 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq75 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq12
    | (have j0 := eq12 X0 (σ X0)
       have j1 := eq75 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq75 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq75 X0 X1
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq817 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq807 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq818 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq817 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817
  have eq823 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq818 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq818
    | (have j0 := eq818 X0 X1
       grind)
    | exact resolve eq818 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818
  have eq824 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq823 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq823
  have eq2143 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 (M.op X0 (M.op X1 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq497 X0 (M.op X1 x) (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq497
    | exact resolve eq497 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq2413 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X0 X1)
       have i₂ := eq504 X1 X0
       grind)
    | exact superpose eq504 eq14
    | exact resolve eq14 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3365 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y (M.op (M.op x X0) y)) y)) := by
    intro X0
    first
    | exact superpose eq545 eq557
    | exact resolve eq557 eq545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq545 eq557
  have eq3399 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op x X0) y)) := by
    intro X0
    first
    | (have i₁ := eq3365 X0
       have i₂ := eq504 y (M.op x X0)
       grind)
    | exact superpose eq504 eq3365
    | exact resolve eq3365 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3365
  have eq3552 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (M.op (σ x) X0) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq549 eq560
    | exact resolve eq560 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549 eq560
  have eq3584 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3552 X0
       have i₂ := eq504 sF3 (M.op sF2 X0)
       grind)
    | exact superpose eq504 eq3552
    | exact resolve eq3552 eq504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504 eq3552
  have eq6638 : (M.op y y) = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq3399 eq533
    | exact resolve eq533 eq3399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3399
  have eq6643 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq3584 eq533
    | exact resolve eq533 eq3584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533 eq3584
  have eq7483 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq685 X0 X1 (M.op X0 X0)
       have i₂ := eq53 X0 X0 X1
       grind)
    | exact superpose eq53 eq685
    | exact resolve eq685 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq685
  have eq7602 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7483 X0 X1
       have i₂ := eq2413 X0 X0
       grind)
    | exact superpose eq2413 eq7483
    | exact resolve eq7483 eq2413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2413 eq7483
  have eq7686 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq26 eq7602
    | (have j0 := eq7602 (σ x) (σ y)
       grind)
    | exact resolve eq7602 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7728 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op x X0) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq281 X0 (M.op (M.op x X0) (M.op x X0))
       have i₂ := eq7602 (M.op x X0) y
       grind)
    | exact superpose eq7602 eq281
    | exact resolve eq281 eq7602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq281
  have eq7730 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op (σ x) X0) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq287 X0 (M.op (M.op sF2 X0) (M.op sF2 X0))
       have i₂ := eq7602 (M.op sF2 X0) sF3
       grind)
    | exact superpose eq7602 eq287
    | exact resolve eq287 eq7602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq7602
  have eq9984 : ∀ X0 : G, (M.op x y) = (M.op (M.op (M.op X0 x) (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq7728 (M.op x (M.op X0 x))
       have i₂ := eq2143 x X0
       grind)
    | exact superpose eq2143 eq7728
    | exact resolve eq7728 eq2143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7728
  have eq10070 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq7730 (M.op sF2 (M.op x sF2))
       have i₂ := eq2143 sF2 x
       grind)
    | exact superpose eq2143 eq7730
    | exact resolve eq7730 eq2143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2143 eq7730
  have eq11508 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq824 X0 X1
       have i₂ := eq119 X0
       grind)
    | exact superpose eq119 eq824
    | (have j0 := eq824 X0 X1
       grind)
    | exact resolve eq824 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq824
  have eq11513 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11508 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq11508
    | exact resolve eq11508 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11539 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq11508 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq11508
    | (have j0 := eq11508 x X0
       grind)
    | exact resolve eq11508 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11508
  have eq11650 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq11539 X0
       have i₂ := eq118
       grind)
    | exact superpose eq118 eq11539
    | (have j0 := eq11539 X0
       grind)
    | exact resolve eq11539 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11539
  have eq11656 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11513 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq11513
    | (have j0 := eq11513 X0 X1
       grind)
    | exact resolve eq11513 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq11513
  have eq11674 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq11656 X0 X1
       have i₂ := eq396 X0
       grind)
    | exact superpose eq396 eq11656
    | (have j0 := eq11656 X0 X1
       grind)
    | exact resolve eq11656 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396 eq11656
  have eq101133 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq11650 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq11650
    | (have j0 := eq11650 y
       grind)
    | exact resolve eq11650 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq11650
  have eq101333 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq101133
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq101133
    | exact resolve eq101133 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101133
  have eq101354 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq101333
    | exact resolve eq101333 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq101333
  have eq101421 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq11674 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq11674
    | (have j0 := eq11674 X1 X1
       grind)
    | exact resolve eq11674 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11674
  have eq102262 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq72
       have i₂ := eq101421 y x
       grind)
    | exact superpose eq101421 eq72
    | (have j1 := eq101421 x x
       grind)
    | exact resolve eq72 eq101421
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq101421
  have eq102492 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq102262
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq102262
    | exact resolve eq102262 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq102262
  have eq102624 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq102492
    | exact resolve eq102492 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102492
  have eq102645 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq102624 eq101354
    | exact resolve eq101354 eq102624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101354 eq102624
  have eq102652 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq102645
       have r₂ := eq27
       grind)
    | exact resolve eq102645 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102645
  have eq102676 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq102652 eq116
    | exact resolve eq116 eq102652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq102652
  have eq102955 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq102676
    | exact resolve eq102676 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq102676
  have eq102956 : x = (M.op x x) := by grind
  clear eq102955
  have eq102975 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq118
       have i₂ := eq102956
       grind)
    | exact superpose eq102956 eq118
    | exact resolve eq118 eq102956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq103037 : (M.op x y) = (M.op (M.op x (M.op x y)) y) := by
    first
    | (have i₁ := eq9984 x
       have i₂ := eq102956
       grind)
    | exact superpose eq102956 eq9984
    | exact resolve eq9984 eq102956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9984 eq102956
  have eq103230 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq6638 eq103037
    | exact resolve eq103037 eq6638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6638 eq103037
  have eq103266 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq102975
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq102975
    | exact resolve eq102975 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq102975
  have eq103516 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq117
       have i₂ := eq103230
       grind)
    | exact superpose eq103230 eq117
    | exact resolve eq117 eq103230
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq103230
  have eq103739 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq103516
    | exact resolve eq103516 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq103516
  have eq104012 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq103266 eq7686
    | exact resolve eq7686 eq103266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7686 eq103266
  have eq104825 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq104012 eq10070
    | exact resolve eq10070 eq104012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10070 eq104012
  have eq104983 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq6643 eq104825
    | exact resolve eq104825 eq6643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6643 eq104825
  have eq105006 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq103739 eq104983
    | exact resolve eq104983 eq103739
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103739 eq104983
  have eq105009 : False := by grind
  exact eq105009

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_x_pyy_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x X0)) = X0 := by
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
  have eq175 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op x y) X0) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 : G, (M.op (σ x) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0))) := by
    intro X0
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq193 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : (M.op x x) = (M.op (M.op (M.op x y) (M.op x x)) (M.op (M.op x y) (M.op x x))) := by
    first
    | exact superpose eq182 eq182
    | exact resolve eq182 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq577 : ∀ X0 X1 : G, (M.op (M.op (M.op x X0) X1) (M.op X0 X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq618 : ∀ X0 : G, (M.op x X0) = (M.op (M.op X0 (M.op x X0)) X0) := by
    intro X0
    first
    | exact superpose eq174 eq184
    | exact resolve eq184 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq625 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op (M.op X1 X0) X2)) = X2 := by
    intro X0 X1 X2
    first
    | exact superpose eq184 eq16
    | exact resolve eq16 eq184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq643 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq646 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq728 : (M.op x y) ≠ (M.op x x) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by
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
  have eq731 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq735 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq740 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq735 eq731
    | (have j1 := eq735 (σ x)
       grind)
    | exact resolve eq731 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq743 : (M.op x y) ≠ (k x x) ∨ x = (M.op x x) ∨ (k y x) = (M.op x x) := by
    first
    | exact superpose eq735 eq728
    | (have j1 := eq735 x
       grind)
    | exact resolve eq728 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq751 : (M.op (σ x) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq735 eq740
    | (have j1 := eq735 (σ x)
       grind)
    | exact resolve eq740 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740
  have eq754 : (M.op x y) ≠ (k x x) ∨ x = (M.op x x) ∨ (k x x) = (k y x) := by
    first
    | exact superpose eq735 eq743
    | (have j1 := eq735 x
       grind)
    | exact resolve eq743 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq846 : (M.op (σ x) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x)))) := by
    first
    | exact superpose eq191 eq191
    | exact resolve eq191 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq945 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op X0 (M.op (σ x) X0)) X0) := by
    intro X0
    first
    | exact superpose eq175 eq193
    | exact resolve eq193 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq193
  have eq1183 : ∀ X0 : G, (M.op (M.op x X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16 X0 X0 (M.op x X0)
       have i₂ := eq618 X0
       grind)
    | exact superpose eq618 eq16
    | exact resolve eq16 eq618
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq618
  have eq1200 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op X0 X0) x X0
       have i₂ := eq1183 X0
       grind)
    | exact superpose eq1183 eq16
    | exact resolve eq16 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1240 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 x) y)) := by
    intro X0
    first
    | (have i₁ := eq625 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq625
    | (have j0 := eq625 x X0 y
       grind)
    | exact resolve eq625 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1248 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 (σ x)) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq625
    | (have j0 := eq625 (σ x) X0 (σ y)
       grind)
    | exact resolve eq625 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1264 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X0 X2)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq625 (M.op X1 X0) (M.op (M.op x X1) X0) X2
       have i₂ := eq577 X1 X0
       grind)
    | exact superpose eq577 eq625
    | exact resolve eq625 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1303 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq625 X0 (M.op x X1) (M.op X1 X0)
       have i₂ := eq577 X1 X0
       grind)
    | exact superpose eq577 eq625
    | exact resolve eq625 eq577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq577 eq625
  have eq1522 : ∀ X0 : G, (M.op (M.op (σ x) X0) (M.op X0 X0)) = X0 := by
    intro X0
    first
    | exact superpose eq945 eq16
    | exact resolve eq16 eq945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq1546 : ∀ X0 : G, (M.op X0 X0) = (M.op X0 (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | exact superpose eq1522 eq16
    | exact resolve eq16 eq1522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1594 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq735 X0
       grind)
    | exact superpose eq735 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq735 X0
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq735 X0
       grind)
    | exact resolve eq13 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1645 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq735 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1648 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1594 X0 X1
       have j1 := eq13 X1 X0
       grind)
    | (have r₁ := eq1594 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq1594 X1 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq1594 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1594
  have eq1835 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1648 (σ X0) X1
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq1648
    | (have j0 := eq1648 (σ X0) X1
       grind)
    | exact resolve eq1648 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2562 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq1264
    | (have j0 := eq1264 (σ x) X0 (σ y)
       grind)
    | exact resolve eq1264 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264
  have eq2794 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X1 X1 (M.op X0 X1)
       have i₂ := eq1303 X1 X0
       grind)
    | exact superpose eq1303 eq16
    | exact resolve eq16 eq1303
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1303
  have eq2955 : ∀ X0 X1 : G, y = (M.op (M.op (M.op X0 x) y) (M.op (M.op (M.op x y) X1) y)) := by
    intro X0 X1
    first
    | exact superpose eq1240 eq177
    | exact resolve eq177 eq1240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1240
  have eq2972 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) X1) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq1248 eq177
    | exact resolve eq177 eq1248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1248
  have eq3051 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq643
       grind)
    | exact superpose eq643 eq39
    | exact resolve eq39 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq3052 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq3051
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq3051
    | exact resolve eq3051 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3051
  have eq3054 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq3052
    | exact resolve eq3052 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3052
  have eq3161 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq2794 X0 X0
       grind)
    | exact superpose eq2794 eq13
    | (have j0 := eq13 X0 X0
       grind)
    | exact resolve eq13 eq2794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4054 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op x X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1200 (M.op x x)
       have i₂ := eq2794 x x
       grind)
    | exact superpose eq2794 eq1200
    | exact resolve eq1200 eq2794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1200
  have eq4178 : (M.op (M.op x y) (M.op x x)) = (M.op (M.op (M.op (M.op x y) (M.op x x)) (M.op (M.op x y) (M.op x x))) (M.op x x)) := by
    first
    | exact superpose eq182 eq4054
    | exact resolve eq4054 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182 eq4054
  have eq4231 : (M.op (M.op x y) (M.op x x)) = (M.op (M.op x x) (M.op x x)) := by
    first
    | exact superpose eq575 eq4178
    | exact resolve eq4178 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq4178
  have eq4235 : x = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq4231
       have i₂ := eq1183 x
       grind)
    | exact superpose eq1183 eq4231
    | exact resolve eq4231 eq1183
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1183 eq4231
  have eq5528 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq1546 (M.op x x)
       have i₂ := eq2794 x x
       grind)
    | exact superpose eq2794 eq1546
    | exact resolve eq1546 eq2794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1546 eq2794
  have eq5681 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x)))) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq191 eq5528
    | exact resolve eq5528 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191 eq5528
  have eq5742 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq846 eq5681
    | exact resolve eq5681 eq846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq846 eq5681
  have eq5747 : (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq1522 eq5742
    | exact resolve eq5742 eq1522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1522 eq5742
  have eq39370 : (M.op (M.op (M.op x y) x) y) = (M.op y y) := by
    first
    | exact superpose eq2955 eq177
    | exact resolve eq177 eq2955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39406 : ∀ X0 : G, y ≠ (M.op (M.op (M.op x y) x) y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq2955 eq3161
    | exact resolve eq3161 eq2955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2955
  have eq40078 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq2972 eq177
    | exact resolve eq177 eq2972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq2972
  have eq68317 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3054 eq646
    | exact resolve eq646 eq3054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68328 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq68317
       have r₂ := eq27
       grind)
    | exact resolve eq68317 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68317
  have eq68336 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq735 eq68328
    | (have j1 := eq735 (σ x)
       grind)
    | exact resolve eq68328 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68328
  have eq68343 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq68336 eq751
    | (have r₁ := eq751
       have r₂ := eq68336
       grind)
    | exact resolve eq751 eq68336
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751 eq68336
  have eq68357 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq68343
  have eq68358 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by grind
  clear eq68357
  have eq68365 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq3054 eq68358
    | exact resolve eq68358 eq3054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3054 eq68358
  have eq68369 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq68365
       have r₂ := eq27
       grind)
    | exact resolve eq68365 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68365
  have eq68461 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq68369 eq3161
    | (have r₁ := eq3161 (σ x) x
       have r₂ := eq68369
       grind)
    | (have r₁ := eq3161 x x
       have r₂ := eq68369
       grind)
    | exact resolve eq3161 eq68369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68369
  have eq68504 : ∀ X0 : G, (M.op x y) = (M.op x x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq68461 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68461
  have eq68885 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ x = (M.op x y) ∨ (M.op x y) = (k x x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 x x
       have i₂ := eq68504 X0
       grind)
    | (have i₁ := eq12 X0 x
       have i₂ := eq68504 (M.op x X0)
       grind)
    | exact superpose eq68504 eq12
    | (have j0 := eq12 X0 x
       have j1 := eq68504 X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq68504 X0
       grind)
    | exact resolve eq12 eq68504
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68924 : ∀ X0 : G, x ≠ (M.op x y) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq68504 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68504
  have eq68925 : ∀ X0 : G, x = (M.op x y) ∨ (M.op x y) = (k x x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq68885 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68885
  have eq68928 : ∀ X0 : G, (M.op x y) = (k x x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq68925 X0
       have j1 := eq68924 X0
       grind)
    | (have r₁ := eq68925 X0
       have r₂ := eq68924 X0
       grind)
    | exact resolve eq68925 eq68924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68924 eq68925
  have eq69335 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ x = (M.op x x) ∨ (M.op x y) = (k y x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq754
       have i₂ := eq68928 X0
       grind)
    | (have i₁ := eq754
       have i₂ := eq68928 (k x x)
       grind)
    | exact superpose eq68928 eq754
    | (have j1 := eq68928 X0
       grind)
    | (have r₁ := eq754
       have r₂ := eq68928 X0
       grind)
    | exact resolve eq754 eq68928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq69340 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq39 x
       have i₂ := eq68928 X0
       grind)
    | (have i₁ := eq39 X0
       have i₂ := eq68928 (k X0 x)
       grind)
    | exact superpose eq68928 eq39
    | (have j1 := eq68928 X0
       grind)
    | exact resolve eq39 eq68928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68928
  have eq69349 : ∀ X0 : G, (M.op x y) ≠ (M.op x y) ∨ x = (M.op x x) ∨ (M.op x y) = (k y x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq69335 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69335
  have eq69350 : ∀ X0 : G, (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq69349 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69349
  have eq69352 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq69340 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq69340
    | (have j0 := eq69340 X0
       grind)
    | exact resolve eq69340 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69340
  have eq69357 : ∀ X0 : G, (σ (M.op x y)) = (k (σ x) (σ x)) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq20 eq69352
    | (have j0 := eq69352 X0
       grind)
    | exact resolve eq69352 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69352
  have eq69648 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq39 y
       have i₂ := eq69350 X0
       grind)
    | (have i₁ := eq39 X0
       have i₂ := eq69350 (k X0 x)
       grind)
    | exact superpose eq69350 eq39
    | (have j1 := eq69350 X0
       grind)
    | exact resolve eq39 eq69350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq69350
  have eq69653 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq69648 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq69648
    | (have j0 := eq69648 X0
       grind)
    | exact resolve eq69648 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69648
  have eq69657 : ∀ X0 : G, (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq69653
    | (have j0 := eq69653 X0
       grind)
    | exact resolve eq69653 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69653
  have eq69948 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq646
       have i₂ := eq69657 (k sF3 sF2)
       grind)
    | exact superpose eq69657 eq646
    | (have j1 := eq69657 X0
       grind)
    | exact resolve eq646 eq69657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646 eq69657
  have eq69960 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq69948 X0
       have j1 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq69948 X0
       have r₂ := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq69948 X0
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq69948 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69948
  have eq69968 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq69960 X0
       grind)
    | (have r₁ := eq69960 X0
       have r₂ := eq27
       grind)
    | exact resolve eq69960 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69960
  have eq72797 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (k X0 (σ x)) = X0 ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq69968 X0
       have i₂ := eq735 sF2
       grind)
    | exact superpose eq735 eq69968
    | (have j0 := eq69968 X0
       have j1 := eq735 x
       grind)
    | exact resolve eq69968 eq735
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq69968
  have eq72948 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq72797 X0
       have j1 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq72797 X0
       have r₂ := eq13 X0 x
       grind)
    | (have r₁ := eq72797 X0
       have r₂ := eq13 X0 (σ x)
       grind)
    | exact resolve eq72797 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72797
  have eq72951 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | exact superpose eq69357 eq72948
    | (have j0 := eq72948 X0
       have j1 := eq69357 X0
       grind)
    | exact resolve eq72948 eq69357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69357 eq72948
  have eq72952 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq72951 X0
       grind)
    | (have r₁ := eq72951 X0
       have r₂ := eq27
       grind)
    | exact resolve eq72951 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72951
  have eq73047 : ∀ X0 X1 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3161 x X1
       have i₂ := eq72952 X0
       grind)
    | exact superpose eq72952 eq3161
    | (have j1 := eq72952 X1
       grind)
    | (have r₁ := eq3161 x X1
       have r₂ := eq72952 X0
       grind)
    | exact resolve eq3161 eq72952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3161 eq72952
  have eq73091 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq73047 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73047
  have eq73339 : ∀ X0 : G, (τ (σ x)) = (k x (τ (σ x))) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq90 X0
       have i₂ := eq73091 (k sF2 X0) x
       grind)
    | exact superpose eq73091 eq90
    | (have j1 := eq73091 X0 x
       grind)
    | exact resolve eq90 eq73091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90 eq73091
  have eq73356 : ∀ X0 : G, x = (k x x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq29 eq73339
    | (have j0 := eq73339 x
       grind)
    | exact resolve eq73339 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq73339
  have eq73418 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq73356 X0
       have j1 := eq1648 x X0
       grind)
    | (have r₁ := eq73356 X0
       have r₂ := eq1648 x x
       grind)
    | (have r₁ := eq73356 x
       have r₂ := eq1648 x x
       grind)
    | exact resolve eq73356 eq1648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648 eq73356
  have eq73452 : x ≠ x ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1645 x
       have i₂ := eq73418 x
       grind)
    | exact superpose eq73418 eq1645
    | (have j0 := eq1645 x
       grind)
    | (have r₁ := eq1645 x
       have r₂ := eq73418 x
       grind)
    | exact resolve eq1645 eq73418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73487 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq35 x
       have i₂ := eq73418 x
       grind)
    | exact superpose eq73418 eq35
    | exact resolve eq35 eq73418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq73418
  have eq73499 : x = (M.op x x) := by grind
  clear eq73452
  have eq73512 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq73487
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq73487
    | exact resolve eq73487 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq73487
  have eq73594 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq4235
       have i₂ := eq73499
       grind)
    | exact superpose eq73499 eq4235
    | exact resolve eq4235 eq73499
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4235 eq73499
  have eq73786 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq73512 eq1645
    | (have j0 := eq1645 (σ x)
       grind)
    | (have r₁ := eq1645 (σ x)
       have r₂ := eq73512
       grind)
    | exact resolve eq1645 eq73512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645 eq73512
  have eq73787 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq73786
  have eq73971 : (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq73594 eq39370
    | exact resolve eq39370 eq73594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39370
  have eq73975 : ∀ X0 : G, y ≠ (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq73594 eq39406
    | (have j0 := eq39406 X0
       grind)
    | exact resolve eq39406 eq73594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39406 eq73594
  have eq74087 : ∀ X0 : G, y ≠ (M.op x y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq73975 X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq73975
    | (have j0 := eq73975 X0
       grind)
    | exact resolve eq73975 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73975
  have eq74091 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq73971
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq73971
    | exact resolve eq73971 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq73971
  have eq74241 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq73787 eq5747
    | exact resolve eq5747 eq73787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5747
  have eq74296 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq73787 eq2562
    | exact resolve eq2562 eq73787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2562 eq73787
  have eq74390 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq26 eq74296
    | exact resolve eq74296 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74296
  have eq74507 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y y) := by
    first
    | (have i₁ := eq12 y y
       have i₂ := eq74091
       grind)
    | exact superpose eq74091 eq12
    | exact resolve eq12 eq74091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74091
  have eq74548 : (M.op x y) = (k y y) ∨ y = (M.op x y) := by grind
  clear eq74507
  have eq74558 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq74241 eq40078
    | exact resolve eq40078 eq74241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40078 eq74241
  have eq74678 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq74558
    | exact resolve eq74558 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq74558
  have eq74752 : ∀ X0 : G, (σ y) ≠ (M.op (σ x) (σ y)) ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq74390 eq13
    | (have j0 := eq13 X0 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq13 eq74390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74390
  have eq74919 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq74678 eq12
    | exact resolve eq12 eq74678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74678
  have eq74960 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq74919
  have eq87164 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq74548
       grind)
    | exact superpose eq74548 eq40
    | exact resolve eq40 eq74548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq74548
  have eq87172 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq87164
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq87164
    | exact resolve eq87164 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87164
  have eq87177 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq87172
    | exact resolve eq87172 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87172
  have eq87498 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq87177 eq74960
    | exact resolve eq74960 eq87177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87513 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq87498
       have r₂ := eq27
       grind)
    | exact resolve eq87498 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87498
  have eq87523 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq87513 eq27
    | exact resolve eq27 eq87513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87785 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq87513 eq74752
    | (have r₁ := eq74752 X0
       have r₂ := eq87513
       grind)
    | exact resolve eq74752 eq87513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74752 eq87513
  have eq87794 : ∀ X0 : G, (k X0 (σ y)) = X0 ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq87785 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87785
  have eq90872 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq87794 eq87177
    | exact resolve eq87177 eq87794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87177
  have eq90873 : (τ (σ y)) = (k y (τ (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq87794 eq107
    | exact resolve eq107 eq87794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq87794
  have eq90874 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq90872
  have eq90882 : y = (k y y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq31 eq90873
    | exact resolve eq90873 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq90873
  have eq90883 : y = (M.op x y) := by
    first
    | (have r₁ := eq90874
       have r₂ := eq87523
       grind)
    | exact resolve eq90874 eq87523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87523 eq90874
  have eq90946 : y = (k y y) := by
    first
    | (have j1 := eq74087 y
       grind)
    | (have r₁ := eq90882
       have r₂ := eq74087 x
       grind)
    | exact resolve eq90882 eq74087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74087 eq90882
  have eq90951 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq90946
       have i₂ := eq90883
       grind)
    | exact superpose eq90883 eq90946
    | exact resolve eq90946 eq90883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90946
  have eq90956 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq90883
       grind)
    | exact superpose eq90883 eq24
    | exact resolve eq24 eq90883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq90883
  have eq91290 : (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq90956 eq20
    | exact resolve eq20 eq90956
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90956
  have eq91859 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq90951 eq1835
    | (have j0 := eq1835 (M.op x y) X0
       grind)
    | exact resolve eq1835 eq90951
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835 eq90951
  have eq91864 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq91859 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91859
  have eq91869 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq91864
    | (have j0 := eq91864 X0
       grind)
    | exact resolve eq91864 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq91864
  have eq91874 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq91290 eq91869
    | exact resolve eq91869 eq91290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91869
  have eq92549 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq91874 eq74960
    | exact resolve eq74960 eq91874
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74960 eq91874
  have eq92552 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq92549
  have eq92744 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | exact superpose eq92552 eq27
    | exact resolve eq27 eq92552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq92552
  have eq93066 : False := by grind
  exact eq93066

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxx_pxy_pyx_Equation2165 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x X0)) = X0 := by
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
  have eq175 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq674 : (M.op x y) = (k y x) ∨ x = y ∨ x = (M.op x x) := by
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
  have eq690 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
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
  have eq702 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq703 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq702 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq702 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq702 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq702
  have eq705 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 X1) X0) (k X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X0 X1
       have i₂ := eq703 X0
       grind)
    | exact superpose eq703 eq16
    | exact resolve eq16 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq713 : x = (M.op (M.op (M.op x y) x) (k x x)) := by
    first
    | (have i₁ := eq174 x
       have i₂ := eq703 x
       grind)
    | exact superpose eq703 eq174
    | exact resolve eq174 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174
  have eq721 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq175 sF2
       have i₂ := eq703 sF2
       grind)
    | exact superpose eq703 eq175
    | exact resolve eq175 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1193 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq176 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq176
    | (have j0 := eq176 x X0 X1 y
       grind)
    | exact resolve eq176 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1202 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X1) (σ x)) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1289 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq176 X0 X1 x (M.op X1 X0)
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq176
    | exact resolve eq176 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq1824 : y = (M.op (M.op x y) (M.op (M.op x x) y)) := by
    first
    | exact superpose eq713 eq1193
    | exact resolve eq1193 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713 eq1193
  have eq1892 : y = (M.op (M.op x y) (M.op (k x x) y)) := by
    first
    | (have i₁ := eq1824
       have i₂ := eq703 x
       grind)
    | exact superpose eq703 eq1824
    | exact resolve eq1824 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824
  have eq2033 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) (σ x)) (σ y))) := by
    first
    | exact superpose eq721 eq1202
    | exact resolve eq1202 eq721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721 eq1202
  have eq2105 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (k (σ x) (σ x)) (σ y))) := by
    first
    | (have i₁ := eq2033
       have i₂ := eq703 sF2
       grind)
    | exact superpose eq703 eq2033
    | exact resolve eq2033 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2033
  have eq2616 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (k X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq705 X1 (M.op X0 X1)
       have i₂ := eq1289 X1 X0
       grind)
    | exact superpose eq1289 eq705
    | exact resolve eq705 eq1289
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq705 eq1289
  have eq2652 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq674
       grind)
    | exact superpose eq674 eq39
    | exact resolve eq39 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq2653 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2652
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2652
    | exact resolve eq2652 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2652
  have eq2655 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq2653
    | exact resolve eq2653 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2653
  have eq2657 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq2655
       have i₂ := eq703 x
       grind)
    | exact superpose eq703 eq2655
    | exact resolve eq2655 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2655
  have eq2671 : ∀ X0 : G, (M.op (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2616 X0 X0
       have i₂ := eq703 X0
       grind)
    | exact superpose eq703 eq2616
    | exact resolve eq2616 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2616
  have eq2776 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2671 X0
       have i₂ := eq703 (k X0 X0)
       grind)
    | exact superpose eq703 eq2671
    | exact resolve eq2671 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2671
  have eq27009 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq2657 eq690
    | exact resolve eq690 eq2657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690 eq2657
  have eq27020 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq27009
       have r₂ := eq27
       grind)
    | exact resolve eq27009 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27009
  have eq27024 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq27020
       have i₂ := eq703 sF2
       grind)
    | exact superpose eq703 eq27020
    | exact resolve eq27020 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27020
  have eq27075 : (τ (σ x)) = (k (τ (σ x)) x) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq27024 eq141
    | exact resolve eq141 eq27024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq27024
  have eq27105 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = (k x x) ∨ x = y := by
    first
    | exact superpose eq29 eq27075
    | exact resolve eq27075 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27075
  have eq27106 : x = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq27105
  have eq27119 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1892
       have i₂ := eq27106
       grind)
    | exact superpose eq27106 eq1892
    | exact resolve eq1892 eq27106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1892
  have eq27126 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq27106
       grind)
    | exact superpose eq27106 eq39
    | exact resolve eq39 eq27106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27106
  have eq27156 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq27126
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27126
    | exact resolve eq27126 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27126
  have eq27159 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq27119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq27119
    | exact resolve eq27119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27119
  have eq27161 : y = (k (M.op x y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq27159
       have i₂ := eq703 sF0
       grind)
    | exact superpose eq703 eq27159
    | exact resolve eq27159 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27159
  have eq27169 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27156 eq2105
    | exact resolve eq2105 eq27156
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2105 eq27156
  have eq27209 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq26 eq27169
    | exact resolve eq27169 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27169
  have eq27212 : (σ y) = (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq27209
       have i₂ := eq703 sF4
       grind)
    | exact superpose eq703 eq27209
    | exact resolve eq27209 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27209
  have eq27250 : (M.op x y) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27161 eq2776
    | exact resolve eq2776 eq27161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27161
  have eq27301 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27212 eq2776
    | exact resolve eq2776 eq27212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2776 eq27212
  have eq27577 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27301 eq115
    | exact resolve eq115 eq27301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115 eq27301
  have eq27626 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27250 eq27577
    | exact resolve eq27577 eq27250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27250 eq27577
  have eq27629 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27626 eq14
    | exact resolve eq14 eq27626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27626
  have eq27640 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq27629
    | exact resolve eq27629 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27629
  have eq27643 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq27640
       have r₂ := eq27
       grind)
    | exact resolve eq27640 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27640
  have eq27645 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq27643 eq31
    | exact resolve eq31 eq27643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq27643
  have eq27759 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq27645
    | exact resolve eq27645 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq27645
  have eq27760 : x = y := by grind
  clear eq27759
  have eq27848 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq27760
       grind)
    | exact superpose eq27760 eq18
    | exact resolve eq18 eq27760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq27849 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq27760
       grind)
    | exact superpose eq27760 eq24
    | exact resolve eq24 eq27760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq27760
  have eq27948 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq27849
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq27849
    | exact resolve eq27849 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27849
  have eq27949 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq27848
       have i₂ := eq703 x
       grind)
    | exact superpose eq703 eq27848
    | exact resolve eq27848 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27848
  have eq27951 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq27948 eq26
    | exact resolve eq26 eq27948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq27948
  have eq28067 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq27951
       have i₂ := eq703 sF2
       grind)
    | exact superpose eq703 eq27951
    | exact resolve eq27951 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703 eq27951
  have eq28083 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq27949
       grind)
    | exact superpose eq27949 eq39
    | exact resolve eq39 eq27949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq27949
  have eq28110 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq28083
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28083
    | exact resolve eq28083 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq28083
  have eq28116 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28067 eq28110
    | exact resolve eq28110 eq28067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28067 eq28110
  have eq28118 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq28116
    | exact resolve eq28116 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq28116
  have eq28120 : False := by grind
  exact eq28120

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pxy_pyx_Equation2165 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op x X0)) = X0 := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) X0) (M.op (σ x) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) y) (M.op x y)) := by
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
  have eq58 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq14 X0 X1 X2
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
  clear eq52
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq92 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq93 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq97 : (σ (k y y)) = (M.op (σ y) (σ y)) := by grind
  clear eq93
  have eq98 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq97
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq92
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq92
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op y x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq99
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq99
    | exact resolve eq99 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq106 : (M.op y x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq105
    | exact resolve eq105 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq214 : y = (M.op (M.op (M.op x y) y) (M.op x y)) := by
    first
    | (have i₁ := eq53 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 y
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq215 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op (M.op x y) (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : (M.op x y) = (M.op y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq214 eq14
    | exact resolve eq14 eq214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq214
  have eq221 : (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq27 eq54
    | (have j0 := eq54 (σ y)
       grind)
    | exact resolve eq54 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (M.op (M.op (σ x) (σ y)) X0) X1)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq225 : (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq221 eq14
    | exact resolve eq14 eq221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221
  have eq235 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op x X0) (M.op x y))) := by
    intro X0
    first
    | exact superpose eq57 eq14
    | exact resolve eq14 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq239 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op (M.op (σ x) X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq58 eq14
    | exact resolve eq14 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq389 : ∀ X1 : G, (M.op (M.op (M.op (σ x) (σ y)) X1) (M.op (σ y) X1)) = X1 := by
    intro X1
    first
    | exact superpose eq239 eq14
    | exact resolve eq14 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq408 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (M.op (σ X0) X1) (σ X0)) (σ (M.op X0 X0))) := by
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
  have eq495 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op X0 X1) x) y)) := by
    intro X0 X1
    first
    | (have i₁ := eq55 x X0 X1 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq55
    | (have j0 := eq55 x X0 X1 y
       grind)
    | exact resolve eq55 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq528 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1 x (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (M.op X2 (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 X1 (M.op (M.op X0 x) (M.op X0 X1))
       have i₂ := eq56 X1 X0 x
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0)
       have i₂ := eq55 X1 x x X0
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq571 : ∀ X0 : G, (M.op y X0) = (M.op X0 (M.op (M.op x y) (M.op y X0))) := by
    intro X0
    first
    | exact superpose eq235 eq56
    | exact resolve eq56 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq575 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) := by
    intro X0
    first
    | exact superpose eq239 eq56
    | exact resolve eq56 eq239
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq579 : ∀ X0 X1 : G, (M.op (M.op x X0) (M.op (M.op (M.op (M.op x y) X0) X1) X0)) = X0 := by
    intro X0 X1
    first
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq585 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op (M.op x X0) y) X1) y)) := by
    intro X0 X1
    first
    | exact superpose eq57 eq56
    | exact resolve eq56 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (M.op (σ x) X0) (σ y)) X1) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq58 eq56
    | exact resolve eq56 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (M.op (M.op (σ X0) X1) (σ (M.op X0 X0)))) := by
    intro X0 X1
    first
    | (have i₁ := eq56 (σ X0) (σ X0) x
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq56
    | exact resolve eq56 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq606 : ∀ X0 : G, (M.op x y) = (M.op y (M.op (M.op X0 x) (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq235 (M.op (M.op X0 x) (M.op X0 x))
       have i₂ := eq56 x X0 x
       grind)
    | exact superpose eq56 eq235
    | exact resolve eq235 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq613 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 (σ x)) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq58 (M.op (M.op x x) (M.op x sF2))
       have i₂ := eq56 sF2 x x
       grind)
    | exact superpose eq56 eq58
    | exact resolve eq58 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq745 : ∀ X0 X1 X2 X3 : G, (M.op X1 X3) = (M.op (M.op (M.op X0 (M.op (M.op X1 X2) X3)) (M.op X1 X3)) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq59 X3 X1 X2 (M.op (M.op X0 x) (M.op X0 (M.op (M.op X1 X2) X3)))
       have i₂ := eq56 (M.op (M.op X1 X2) X3) X0 x
       grind)
    | exact superpose eq56 eq59
    | exact resolve eq59 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq749 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X4) X0) (M.op X1 X0)) = X0 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq59 (M.op X1 X0) (M.op (M.op X1 X2) X0) X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq59
    | exact resolve eq59 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq775 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq59 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq59 eq59
    | exact resolve eq59 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq792 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq72 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq72
    | (have j0 := eq72 X0 X1
       grind)
    | exact resolve eq72 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq893 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ x)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq792 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq792
    | (have j0 := eq792 X0 x
       grind)
    | exact resolve eq792 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq792
  have eq1307 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y))) := by
    first
    | exact superpose eq27 eq224
    | (have j0 := eq224 (σ x) (σ y)
       grind)
    | exact resolve eq224 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224
  have eq1423 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op X0 (M.op y (M.op (M.op x y) X0))) := by
    intro X0
    first
    | exact superpose eq495 eq56
    | exact resolve eq56 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495
  have eq1924 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X0 X1)
       have i₂ := eq528 X1 X0
       grind)
    | exact superpose eq528 eq14
    | exact resolve eq14 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2868 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (M.op x (M.op (M.op x y) X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq579 (M.op sF0 X0) X0
       have i₂ := eq14 X0 sF0 (M.op sF0 X0)
       grind)
    | exact superpose eq14 eq579
    | exact resolve eq579 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq3004 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op y (M.op (M.op x X0) y)) y)) := by
    intro X0
    first
    | exact superpose eq571 eq585
    | exact resolve eq585 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571 eq585
  have eq3033 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op x X0) y)) := by
    intro X0
    first
    | (have i₁ := eq3004 X0
       have i₂ := eq528 y (M.op x X0)
       grind)
    | exact superpose eq528 eq3004
    | exact resolve eq3004 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3004
  have eq3115 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ y) (M.op (M.op (σ x) X0) (σ y))) (σ y))) := by
    intro X0
    first
    | exact superpose eq575 eq588
    | exact resolve eq588 eq575
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq575 eq588
  have eq3142 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (σ x) X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq3115 X0
       have i₂ := eq528 sF3 (M.op sF2 X0)
       grind)
    | exact superpose eq528 eq3115
    | exact resolve eq3115 eq528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq528 eq3115
  have eq5067 : (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op x x)) := by
    first
    | exact superpose eq215 eq2868
    | exact resolve eq2868 eq215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq2868
  have eq5123 : x = (M.op (M.op x y) (M.op x x)) := by
    first
    | (have i₁ := eq5067
       have i₂ := eq1924 x x
       grind)
    | exact superpose eq1924 eq5067
    | exact resolve eq5067 eq1924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5067
  have eq5240 : x = (M.op (M.op x x) (M.op y x)) := by
    first
    | exact superpose eq5123 eq1423
    | exact resolve eq1423 eq5123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1423 eq5123
  have eq5978 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op X1 (M.op (σ X0) (M.op (σ (M.op X0 X0)) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq555 (M.op (M.op (σ X0) x) (σ X0)) (σ (M.op X0 X0)) X1
       have i₂ := eq408 X0 x
       grind)
    | exact superpose eq408 eq555
    | exact resolve eq555 eq408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq408 eq555
  have eq6514 : (M.op y y) = (M.op (M.op x (M.op x y)) y) := by
    first
    | exact superpose eq3033 eq556
    | exact resolve eq556 eq3033
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3033
  have eq6519 : (M.op (σ y) (σ y)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ y)) := by
    first
    | exact superpose eq3142 eq556
    | exact resolve eq556 eq3142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3142
  have eq6637 : y = (M.op (M.op y y) (M.op x y)) := by
    first
    | exact superpose eq6514 eq57
    | exact resolve eq57 eq6514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq6514
  have eq6707 : (σ y) = (M.op (M.op (σ y) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6519 eq58
    | exact resolve eq58 eq6519
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58 eq6519
  have eq7718 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq775 X0 X1 (M.op X0 X0)
       have i₂ := eq56 X0 X0 X1
       grind)
    | exact superpose eq56 eq775
    | exact resolve eq775 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq7723 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op y x) (M.op x y)) := by
    first
    | exact superpose eq606 eq775
    | exact resolve eq775 eq606
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq606
  have eq7737 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq1307 eq775
    | exact resolve eq775 eq1307
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1307
  have eq7840 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7718 X0 X1
       have i₂ := eq1924 X0 X0
       grind)
    | exact superpose eq1924 eq7718
    | exact resolve eq7718 eq1924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7718
  have eq7995 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq556 X1 X0 (M.op X0 X0)
       have i₂ := eq7840 X0 X1
       grind)
    | exact superpose eq7840 eq556
    | exact resolve eq556 eq7840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7840
  have eq10447 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq775 (σ X0) X1 (σ (M.op X0 X0))
       have i₂ := eq589 X0 X1
       grind)
    | exact superpose eq589 eq775
    | exact resolve eq775 eq589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589 eq775
  have eq10486 : ∀ X0 X1 : G, (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10447 X0 X1
       have i₂ := eq45 (M.op X0 X0)
       grind)
    | exact superpose eq45 eq10447
    | exact resolve eq10447 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq10447
  have eq10508 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (σ X0) X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq10486 X0 X1
       have i₂ := eq1924 X0 X0
       grind)
    | exact superpose eq1924 eq10486
    | exact resolve eq10486 eq1924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1924 eq10486
  have eq19346 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (M.op X0 X2) X1)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq749 X1 (M.op X0 X2) x x (M.op X0 X1)
       have i₂ := eq745 (M.op (M.op (M.op (M.op X0 X2) x) X1) x) X0 X2 X1
       grind)
    | exact superpose eq745 eq749
    | exact resolve eq749 eq745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq745 eq749
  have eq19934 : ∀ X0 : G, (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X0) (M.op (M.op (σ y) (σ y)) X0)) = X0 := by
    intro X0
    first
    | exact superpose eq7737 eq19346
    | exact resolve eq19346 eq7737
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7737
  have eq20175 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op (M.op X1 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq556 (M.op X1 X0) X1 X0
       have i₂ := eq19346 X1 X0 (M.op X1 X0)
       grind)
    | exact superpose eq19346 eq556
    | exact resolve eq556 eq19346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19346
  have eq20708 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq893 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq893
    | (have j0 := eq893 y
       grind)
    | exact resolve eq893 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq893
  have eq20793 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20708
       have i₂ := eq92
       grind)
    | exact superpose eq92 eq20708
    | exact resolve eq20708 eq92
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20708
  have eq20807 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq20793
    | exact resolve eq20793 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20793
  have eq20820 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq20807
       have i₂ := eq98
       grind)
    | exact superpose eq98 eq20807
    | exact resolve eq20807 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20807
  have eq42556 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ y) (σ y)) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq6707 eq20175
    | exact resolve eq20175 eq6707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6707 eq20175
  have eq53564 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X0)) (M.op X1 (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq556 X1 (σ X0) (σ (M.op X0 X0))
       have i₂ := eq10508 X0 X1
       grind)
    | exact superpose eq10508 eq556
    | exact resolve eq556 eq10508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556 eq10508
  have eq82569 : y = (M.op (M.op y x) (M.op x y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq6637
       have i₂ := eq106
       grind)
    | exact superpose eq106 eq6637
    | exact resolve eq6637 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6637
  have eq82728 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq7723 eq82569
    | exact resolve eq82569 eq7723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7723 eq82569
  have eq137111 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (σ y))) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq19934 (M.op x sF3)
       have i₂ := eq7995 sF3 x
       grind)
    | exact superpose eq7995 eq19934
    | exact resolve eq19934 eq7995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19934
  have eq223870 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq82728 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq82728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq223879 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq27 eq223870
    | exact resolve eq223870 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223870
  have eq223890 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have r₁ := eq223879
       have r₂ := eq28
       grind)
    | exact resolve eq223879 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223879
  have eq223917 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op (σ y) (σ x)) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq223890 eq42556
    | exact resolve eq42556 eq223890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42556
  have eq223962 : (M.op (σ y) (σ x)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ y) (σ x))) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq223890 eq137111
    | exact resolve eq137111 eq223890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137111 eq223890
  have eq224154 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | (have i₁ := eq223962
       have i₂ := eq389 (M.op (M.op sF4 sF2) (M.op sF3 sF2))
       grind)
    | exact superpose eq389 eq223962
    | exact resolve eq223962 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223962
  have eq224155 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq613 eq223917
    | exact resolve eq223917 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613 eq223917
  have eq224157 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq27 eq224154
    | exact resolve eq224154 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224154
  have eq224158 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq224155 eq225
    | exact resolve eq225 eq224155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq225
  have eq224266 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq224155 eq7995
    | exact resolve eq7995 eq224155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224155
  have eq224439 : (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq224157 eq389
    | exact resolve eq389 eq224157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq389 eq224157
  have eq228172 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ y) (σ y)) ∨ (σ y) = (M.op X0 (M.op (σ x) (σ y))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    intro X0
    first
    | exact superpose eq224266 eq12
    | (have j0 := eq12 (σ y) (M.op X0 (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq12 eq224266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224266
  have eq228326 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ y) (M.op X0 (M.op (σ x) (σ y)))) ∨ (σ y) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq228172 X0
       grind)
    | (have r₁ := eq228172 X0
       have r₂ := eq224158
       grind)
    | exact resolve eq228172 eq224158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224158 eq228172
  have eq551438 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq224439 eq228326
    | exact resolve eq228326 eq224439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224439 eq228326
  have eq551520 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by grind
  clear eq551438
  have eq551546 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq551520 eq82728
    | exact resolve eq82728 eq551520
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82728 eq551520
  have eq551557 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq551546
  have eq551560 : y = (M.op (M.op x y) (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq551557
       have r₂ := eq28
       grind)
    | exact resolve eq551557 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551557
  have eq551569 : (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq551560 eq218
    | exact resolve eq218 eq551560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218
  have eq551704 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ (M.op x y)) (M.op (σ y) X0))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq551560 eq5978
    | exact resolve eq5978 eq551560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5978
  have eq551708 : ∀ X0 : G, (M.op x y) = (M.op y (M.op X0 (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq551560 eq7995
    | exact resolve eq7995 eq551560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7995 eq551560
  have eq551956 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ (M.op x y)) (M.op (σ y) X0))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq551704 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq551704
    | (have j0 := eq551704 X0
       grind)
    | exact resolve eq551704 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551704
  have eq551999 : ∀ X0 : G, (M.op (σ y) X0) = (M.op X0 (M.op (σ (M.op x y)) (M.op (σ y) X0))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq21 eq551956
    | (have j0 := eq551956 X0
       grind)
    | exact resolve eq551956 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551956
  have eq552019 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq98
       have i₂ := eq551569
       grind)
    | exact superpose eq551569 eq98
    | exact resolve eq98 eq551569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq552020 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq551569
       grind)
    | exact superpose eq551569 eq106
    | exact resolve eq106 eq551569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq552165 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op X0 (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq53564 y X0
       have i₂ := eq551569
       grind)
    | exact superpose eq551569 eq53564
    | exact resolve eq53564 eq551569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53564
  have eq552418 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq552020
  have eq552435 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op X0 (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq552165 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq552165
    | (have j0 := eq552165 X0
       grind)
    | exact resolve eq552165 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552165
  have eq552470 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq552019
    | exact resolve eq552019 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552019
  have eq552471 : ∀ X0 : G, (σ y) = (M.op (σ (M.op x y)) (M.op X0 (σ y))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq21 eq552435
    | (have j0 := eq552435 X0
       grind)
    | exact resolve eq552435 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552435
  have eq554248 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq552470 eq20820
    | exact resolve eq20820 eq552470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552470
  have eq554759 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq554248
  have eq563464 : ∀ X0 : G, (M.op x y) ≠ (M.op y y) ∨ y = (M.op X0 (M.op x y)) ∨ (M.op x y) = (k y (M.op X0 (M.op x y))) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq551708 eq12
    | (have j0 := eq12 y (M.op X0 (M.op x y))
       grind)
    | exact resolve eq12 eq551708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551708
  have eq563719 : ∀ X0 : G, (M.op x y) = (k y (M.op X0 (M.op x y))) ∨ y = (M.op X0 (M.op x y)) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have j0 := eq563464 X0
       grind)
    | (have r₁ := eq563464 X0
       have r₂ := eq551569
       grind)
    | exact resolve eq563464 eq551569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551569 eq563464
  have eq566577 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ x))) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq20820 eq552471
    | exact resolve eq552471 eq20820
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20820 eq552471
  have eq566883 : (σ y) = (M.op (σ (M.op x y)) (M.op (σ y) (σ x))) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq566577
  have eq738778 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq554759 eq552418
    | exact resolve eq552418 eq554759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq738791 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) := by grind
  clear eq738778
  have eq738796 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq738791
       have r₂ := eq28
       grind)
    | exact resolve eq738791 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738791
  have eq1382105 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq566883 eq551999
    | exact resolve eq551999 eq566883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551999 eq566883
  have eq1382617 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1382105
  have eq1382647 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq1382617
    | exact resolve eq1382617 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382617
  have eq1382665 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq1382647 eq552418
    | exact resolve eq552418 eq1382647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552418
  have eq1382682 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq1382665
  have eq1382689 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq1382682
       have r₂ := eq28
       grind)
    | exact resolve eq1382682 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382682
  have eq1386652 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq1382689 eq738796
    | exact resolve eq738796 eq1382689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq738796 eq1382689
  have eq1387282 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq1386652
  have eq1387389 : (M.op x y) = (M.op y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1387282
       have r₂ := eq28
       grind)
    | exact resolve eq1387282 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1387282
  have eq1387397 : x = (M.op (M.op x x) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq5240
       have i₂ := eq1387389
       grind)
    | exact superpose eq1387389 eq5240
    | exact resolve eq5240 eq1387389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5240 eq1387389
  have eq1392200 : (M.op x y) = (k y x) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1387397 eq563719
    | exact resolve eq563719 eq1387397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563719 eq1387397
  have eq1392656 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1392200
  have eq1392740 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq1392656
       grind)
    | exact superpose eq1392656 eq92
    | exact resolve eq92 eq1392656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq1392656
  have eq1392795 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq1392740
    | exact resolve eq1392740 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392740
  have eq1392852 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1392795 eq554759
    | exact resolve eq554759 eq1392795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554759
  have eq1392853 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1392795 eq1382647
    | exact resolve eq1382647 eq1392795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1382647 eq1392795
  have eq1392870 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq1392853
  have eq1392871 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1392852
  have eq1392881 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1392870
       have r₂ := eq28
       grind)
    | exact resolve eq1392870 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392870
  have eq1392882 : (σ (M.op x y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1392871
       have r₂ := eq28
       grind)
    | exact resolve eq1392871 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392871
  have eq1393833 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1392882 eq1392881
    | exact resolve eq1392881 eq1392882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1392881 eq1392882
  have eq1394466 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1393833
  have eq1394590 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq1394466
       have r₂ := eq28
       grind)
    | exact resolve eq1394466 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394466
  have eq1394593 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq1394590 eq30
    | exact resolve eq30 eq1394590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq1394590
  have eq1395051 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq1394593
    | exact resolve eq1394593 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1394593
  have eq1395052 : x = y := by grind
  clear eq1395051
  have eq1395071 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1395052
       grind)
    | exact superpose eq1395052 eq19
    | exact resolve eq19 eq1395052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1395072 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1395052
       grind)
    | exact superpose eq1395052 eq25
    | exact resolve eq25 eq1395052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1395052
  have eq1395648 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1395072
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1395072
    | exact resolve eq1395072 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1395072
  have eq1395679 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1395648 eq27
    | exact resolve eq27 eq1395648
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1395648
  have eq1397110 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1395679 eq71
    | exact resolve eq71 eq1395679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq1395679
  have eq1397935 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1397110
       have i₂ := eq1395071
       grind)
    | exact superpose eq1395071 eq1397110
    | exact resolve eq1397110 eq1395071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395071 eq1397110
  have eq1397986 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1397935 eq15
    | exact resolve eq15 eq1397935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397935
  have eq1398326 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1397986
    | exact resolve eq1397986 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1397986
  have eq1398428 : False := by grind
  exact eq1398428

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_y_pyx_Equation2165 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X2) X0) (M.op X1 X0)) = X0 := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X2) X0) X3)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op X1 X2) X0) (M.op X1 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X0 (M.op (M.op X1 X2) (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op X1 X0) = (M.op (M.op (M.op (M.op (M.op X1 X2) X0) X3) (M.op X1 X0)) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op X1 X0) (M.op (M.op X1 X2) X0) X3
       have i₂ := eq14 X0 X1 X2
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
  clear eq52
  have eq88 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq37
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq88
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq88
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq88 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x x) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq95
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq95
    | exact resolve eq95 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq102 : (M.op x x) = (M.op y y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq101
    | exact resolve eq101 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq521 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X0 (M.op X1 X0)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 X1 x (M.op X1 X0)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq55
    | exact resolve eq55 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq547 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) X2) = (M.op X2 (M.op X0 (M.op (M.op X1 X0) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 (M.op X1 X0) (M.op (M.op (M.op x x) X1) X0)
       have i₂ := eq55 X1 x x X0
       grind)
    | exact superpose eq55 eq56
    | exact resolve eq56 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq708 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 (M.op (M.op X0 X1) X2)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq59 X2 (M.op X0 X1) (M.op (M.op X0 X1) X2) (M.op X0 (M.op (M.op X0 X1) X2))
       have i₂ := eq59 (M.op (M.op X0 X1) X2) X0 X1 X2
       grind)
    | exact superpose eq59 eq59
    | exact resolve eq59 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq1897 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X1 X1)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 (M.op X0 X1)
       have i₂ := eq521 X1 X0
       grind)
    | exact superpose eq521 eq14
    | exact resolve eq14 eq521
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq7618 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq708 X0 X1 (M.op X0 X0)
       have i₂ := eq56 X0 X0 X1
       grind)
    | exact superpose eq56 eq708
    | exact resolve eq708 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq708
  have eq7740 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq7618 X0 X1
       have i₂ := eq1897 X0 X0
       grind)
    | exact superpose eq1897 eq7618
    | exact resolve eq7618 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7618
  have eq7894 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op X1 X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq547 X1 X0 (M.op X0 X0)
       have i₂ := eq7740 X0 X1
       grind)
    | exact superpose eq7740 eq547
    | exact resolve eq547 eq7740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq547
  have eq80015 : y = (M.op (M.op x x) (M.op x x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq7740 y y
       have i₂ := eq102
       grind)
    | exact superpose eq102 eq7740
    | exact resolve eq7740 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102 eq7740
  have eq80024 : x = y ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq80015
       have i₂ := eq1897 x x
       grind)
    | exact superpose eq1897 eq80015
    | exact resolve eq80015 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80015
  have eq80025 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq80024
  have eq80084 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq80025 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq80025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80025
  have eq80092 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq80084
    | exact resolve eq80084 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80084
  have eq80103 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq80092
       have r₂ := eq28
       grind)
    | exact resolve eq80092 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80092
  have eq80258 : (σ y) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq80103 eq7894
    | exact resolve eq7894 eq80103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7894 eq80103
  have eq80264 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq80258
       have i₂ := eq1897 sF2 sF2
       grind)
    | exact superpose eq1897 eq80258
    | exact resolve eq80258 eq1897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1897 eq80258
  have eq80265 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq80264
  have eq80299 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq80265 eq30
    | exact resolve eq30 eq80265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq80265
  have eq80525 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq80299
    | exact resolve eq80299 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq80299
  have eq80526 : x = y := by grind
  clear eq80525
  have eq80545 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq80526
       grind)
    | exact superpose eq80526 eq19
    | exact resolve eq19 eq80526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq80546 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq80526
       grind)
    | exact superpose eq80526 eq25
    | exact resolve eq25 eq80526
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq80526
  have eq80769 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq80546
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq80546
    | exact resolve eq80546 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq80546
  have eq80788 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq80769 eq27
    | exact resolve eq27 eq80769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq80769
  have eq81277 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq80788 eq71
    | exact resolve eq71 eq80788
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq80788
  have eq81466 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq81277
       have i₂ := eq80545
       grind)
    | exact superpose eq80545 eq81277
    | exact resolve eq81277 eq80545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80545 eq81277
  have eq81476 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq81466 eq15
    | exact resolve eq15 eq81466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81466
  have eq81557 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq81476
    | exact resolve eq81476 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq81476
  have eq81578 : False := by grind
  exact eq81578

/-- `Equation2165`: `x = ((y ◇ z) ◇ x) ◇ (y ◇ x)`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pyy_pyx_Equation2165 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2165 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2165.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq845 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (σ X0) = X1 ∨ (σ (M.op X0 X0)) = (k X1 (σ X0)) := by
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
  have eq2562 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq2579 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq2562 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq2562
    | (have j0 := eq2562 X0 X1
       grind)
    | exact resolve eq2562 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2562
  have eq3953 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2579 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq2579
    | (have j0 := eq2579 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | exact resolve eq2579 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq137950 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) ∨ (σ (M.op X0 X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq845 X0 (σ X1)
       have i₂ := eq3953 X0 X1
       grind)
    | exact superpose eq3953 eq845
    | (have j0 := eq845 X0 (σ X1)
       have j1 := eq3953 X0 X1
       grind)
    | (have r₁ := eq845 X0 (σ X1)
       have r₂ := eq3953 X0 X1
       grind)
    | (have r₁ := eq845 X1 (σ X1)
       have r₂ := eq3953 X1 X1
       grind)
    | (have r₁ := eq845 X0 X1
       have r₂ := eq3953 (σ (M.op X0 X0)) (M.op (σ X0) X1)
       grind)
    | exact resolve eq845 eq3953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq138213 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq3953 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3953
  have eq138215 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (σ X0) = (σ X1) ∨ (σ (M.op X0 X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq137950 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137950
  have eq138216 : ∀ X0 X1 : G, (σ X0) = (σ X1) ∨ (σ (M.op X0 X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq138215 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138215
  have eq138332 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq138216 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq138216
    | (have j0 := eq138216 X0 X1
       grind)
    | exact resolve eq138216 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138216
  have eq138454 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | exact superpose eq14 eq138332
    | (have j0 := eq138332 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | exact resolve eq138332 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138332
  have eq138501 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq138454 X0 X1
       have j1 := eq138213 X0 X1
       grind)
    | (have r₁ := eq138454 X0 X1
       have r₂ := eq138213 X0 X1
       grind)
    | (have r₁ := eq138454 X1 X1
       have r₂ := eq138213 X1 X1
       grind)
    | (have r₁ := eq138454 (M.op X0 X0) (M.op X0 X1)
       have r₂ := eq138213 X0 X1
       grind)
    | exact resolve eq138454 eq138213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138213 eq138454
  have eq1994590 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq138501 x y
       grind)
    | exact superpose eq138501 eq16
    | (have j1 := eq138501 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq138501 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq138501 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq138501 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq138501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138501
  have eq1995647 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1994590
  have eq1996153 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (M.op x x) = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq1995647
       grind)
    | exact superpose eq1995647 eq13
    | (have j0 := eq13 x x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1995647
       grind)
    | exact resolve eq13 eq1995647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1997034 : (M.op x x) ≠ (M.op x x) ∨ x = y ∨ (M.op x x) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq1996153
  have eq1997035 : (M.op x x) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq1997034
  have eq1997205 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq2579 x y
       have i₂ := eq1997035
       grind)
    | exact superpose eq1997035 eq2579
    | (have j0 := eq2579 x y
       grind)
    | exact resolve eq2579 eq1997035
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2579 eq1997035
  have eq1997208 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq1997205
  have eq2002446 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq1997208
       grind)
    | exact superpose eq1997208 eq16
    | exact resolve eq16 eq1997208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1997208
  have eq2003773 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1995647 eq2002446
    | exact resolve eq2002446 eq1995647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1995647 eq2002446
  have eq2003774 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2003773
  have eq2003964 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq2003774
       grind)
    | exact superpose eq2003774 eq10
    | exact resolve eq10 eq2003774
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2003774
  have eq2004179 : x = y ∨ x = y := by
    first
    | (have i₁ := eq2003964
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2003964
    | exact resolve eq2003964 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2003964
  have eq2004180 : x = y := by grind
  clear eq2004179
  have eq2004183 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2004180
       grind)
    | exact superpose eq2004180 eq16
    | exact resolve eq16 eq2004180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2004180
  have eq2004184 : False := by grind
  exact eq2004184
