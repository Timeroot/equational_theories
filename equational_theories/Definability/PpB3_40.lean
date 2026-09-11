import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,Y) else if m(Y,Y) = X then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_x_pyy_pyy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
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
  have eq64 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq70 (σ X0)
       grind)
    | exact superpose eq70 eq15
    | exact resolve eq15 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq70 X0
       grind)
    | exact superpose eq70 eq73
    | exact resolve eq73 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq73
  have eq95 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq64 (σ X0) (σ X0)
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq64
    | exact resolve eq64 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (σ X0)
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq12
    | exact resolve eq12 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq577 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq560 X0 X1
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq560
    | (have j0 := eq560 X0 X1
       grind)
    | exact resolve eq560 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq591 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq577 X0 X1
       have i₂ := eq84 X0
       grind)
    | exact superpose eq84 eq577
    | (have j0 := eq577 X0 X1
       grind)
    | exact resolve eq577 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84 eq577
  have eq3855 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq591 X0 X1
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq591
    | (have j0 := eq591 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | exact resolve eq591 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83612 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X0)) ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq97 X0 (σ X1)
       have i₂ := eq3855 X0 X1
       grind)
    | exact superpose eq3855 eq97
    | (have j0 := eq97 X0 (σ X1)
       have j1 := eq3855 X0 X1
       grind)
    | (have r₁ := eq97 X0 (σ X1)
       have r₂ := eq3855 X0 X1
       grind)
    | (have r₁ := eq97 X1 (σ X1)
       have r₂ := eq3855 X1 X1
       grind)
    | (have r₁ := eq97 X0 (σ X0)
       have r₂ := eq3855 (σ X0) (σ (M.op X0 X0))
       grind)
    | exact resolve eq97 eq3855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq83698 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X0 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq3855 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3855
  have eq83700 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq83612 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83612
  have eq83731 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X0)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq83700 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq83700
    | (have j0 := eq83700 X0 X1
       grind)
    | exact resolve eq83700 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83700
  have eq83771 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X0 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | exact superpose eq14 eq83731
    | (have j0 := eq83731 X0 X1
       have j1 := eq14 X1 X0
       grind)
    | exact resolve eq83731 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83731
  have eq83799 : ∀ X0 X1 : G, (σ X1) = (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq83771 X0 X1
       have j1 := eq83698 X0 X1
       grind)
    | (have r₁ := eq83771 X0 X1
       have r₂ := eq83698 X0 X1
       grind)
    | (have r₁ := eq83771 X1 X1
       have r₂ := eq83698 X1 X1
       grind)
    | (have r₁ := eq83771 X1 (M.op X1 X1)
       have r₂ := eq83698 X1 X1
       grind)
    | exact resolve eq83771 eq83698
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83698 eq83771
  have eq83829 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X1) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq83799 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83799
  have eq181480 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq83829 x y
       grind)
    | exact superpose eq83829 eq16
    | (have j1 := eq83829 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq83829 x y
       grind)
    | exact resolve eq16 eq83829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83829
  have eq181687 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq181480
  have eq182037 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq181687
       grind)
    | exact superpose eq181687 eq10
    | exact resolve eq10 eq181687
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181687
  have eq182272 : y = (M.op x x) ∨ y = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq182037
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq182037
    | exact resolve eq182037 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182037
  have eq182273 : (M.op x y) = (M.op x x) ∨ y = (M.op x x) := by grind
  clear eq182272
  have eq182278 : (M.op x x) ≠ (M.op x x) ∨ (M.op x x) = (k y x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq182273
       grind)
    | exact superpose eq182273 eq12
    | (have j0 := eq12 x x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq182273
       grind)
    | exact resolve eq12 eq182273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182408 : (M.op x x) = (k y x) ∨ y = (M.op x x) := by grind
  clear eq182278
  have eq182413 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq591 x y
       have i₂ := eq182408
       grind)
    | exact superpose eq182408 eq591
    | (have j0 := eq591 x y
       grind)
    | exact resolve eq591 eq182408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq591 eq182408
  have eq182425 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq182413
  have eq222310 : (σ (M.op x y)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq182425
       grind)
    | exact superpose eq182425 eq16
    | exact resolve eq16 eq182425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182425
  have eq222533 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq182273 eq222310
    | exact resolve eq222310 eq182273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182273 eq222310
  have eq222534 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq222533
  have eq222631 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq222534
       grind)
    | exact superpose eq222534 eq10
    | exact resolve eq10 eq222534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222534
  have eq222898 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq222631
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq222631
    | exact resolve eq222631 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq222631
  have eq222899 : y = (M.op x x) := by grind
  clear eq222898
  have eq222904 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq95 x
       have i₂ := eq222899
       grind)
    | exact superpose eq222899 eq95
    | exact resolve eq95 eq222899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq223140 : y = (M.op x y) := by
    first
    | (have i₁ := eq64 x x
       have i₂ := eq222899
       grind)
    | exact superpose eq222899 eq64
    | exact resolve eq64 eq222899
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq222899
  have eq223275 : (σ y) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq223140
       grind)
    | exact superpose eq223140 eq16
    | exact resolve eq16 eq223140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq223140
  have eq223443 : False := by grind
  exact eq223443

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_pxx_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq32 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq32 (σ X0)
       grind)
    | exact superpose eq32 eq15
    | exact resolve eq15 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq37 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq32 X0
       grind)
    | exact superpose eq32 eq34
    | exact resolve eq34 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq34
  have eq52 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq14 (σ X1) (σ X0)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq77 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq55 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq55
    | exact resolve eq55 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq199 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq185 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq185
    | (have j0 := eq185 X0 X1
       grind)
    | exact resolve eq185 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq185
  have eq205 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq199 X0 X1
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq199 X1 X0
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq199 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq199 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq199
  have eq262 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq205 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq205
    | exact resolve eq205 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq270 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq205 (σ X1) X0
       grind)
    | exact superpose eq205 eq15
    | (have j1 := eq205 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq293 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq262 (τ X0) X1
       grind)
    | exact superpose eq262 eq19
    | (have j1 := eq262 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq262
  have eq551 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq293 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq293
    | exact resolve eq293 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq293
  have eq582 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq551 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq551
    | (have j0 := eq551 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq551 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551
  have eq1175 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq270 x y
       grind)
    | exact superpose eq270 eq16
    | (have j1 := eq270 x y
       grind)
    | exact resolve eq16 eq270
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq1265 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1175
       have i₂ := eq582 x y
       grind)
    | exact superpose eq582 eq1175
    | (have j1 := eq582 (σ x) (σ y)
       grind)
    | (have r₁ := eq1175
       have r₂ := eq582 x y
       grind)
    | (have r₁ := eq1175
       have r₂ := eq582 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1175
       have r₂ := eq582 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1175 eq582
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582 eq1175
  have eq1266 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1265
  have eq1270 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1266
       grind)
    | exact superpose eq1266 eq10
    | exact resolve eq10 eq1266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1266
  have eq1314 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1270
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1270
    | exact resolve eq1270 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1270
  have eq1315 : x = y := by grind
  clear eq1314
  have eq1380 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1315
       grind)
    | exact superpose eq1315 eq16
    | exact resolve eq16 eq1315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1315
  have eq1381 : False := by grind
  exact eq1381

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyx_pyx_pxx_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq24 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq24 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq24 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq24 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq29 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X1 X0
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
  have eq38 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq41 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq29 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq42 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X1 X1
       grind)
    | (have r₁ := eq38 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq41 X0 X1
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq41 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq52 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq25 X1
       grind)
    | exact superpose eq25 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq46
  have eq53 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       have j1 := eq42 X1 X0
       grind)
    | (have r₁ := eq50 X1 X1
       have r₂ := eq42 X0 X1
       grind)
    | exact resolve eq50 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq50
  have eq167 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq172 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq167 X0 X1
       have j1 := eq52 X1 X0
       grind)
    | (have r₁ := eq167 X1 X0
       have r₂ := eq52 X0 X1
       grind)
    | (have r₁ := eq167 X0 X0
       have r₂ := eq52 X0 X0
       grind)
    | exact resolve eq167 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq167
  have eq229 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq172 (σ X1) (σ X0)
       grind)
    | exact superpose eq172 eq15
    | exact resolve eq15 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq229 X0 X1
       have i₂ := eq172 X1 X0
       grind)
    | exact superpose eq172 eq229
    | exact resolve eq229 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq229
  have eq237 : False := by grind
  exact eq237

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pyx_pxy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq76 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq316 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq76 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq76 X0 X1
       grind)
    | exact superpose eq76 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq76 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq76 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq76 X0 X1
       grind)
    | exact resolve eq13 eq76
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq339 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq316 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq340 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq339 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq339
  have eq346 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq340 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq340 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq340 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq340
  have eq354 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq346 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq346
    | (have j0 := eq346 X0 X1
       grind)
    | exact resolve eq346 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq346
  have eq355 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq354 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq360 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq355 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq355
    | exact resolve eq355 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq372 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq355 x y
       grind)
    | exact superpose eq355 eq16
    | exact resolve eq16 eq355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq355
  have eq434 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq360 X0 (τ X1)
       grind)
    | exact superpose eq360 eq17
    | exact resolve eq17 eq360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq360
  have eq450 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq434 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq434
    | exact resolve eq434 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq434
  have eq457 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq450 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq450
    | exact resolve eq450 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq475 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq372
       have i₂ := eq457 x y
       grind)
    | exact superpose eq457 eq372
    | exact resolve eq372 eq457
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372 eq457
  have eq476 : False := by grind
  exact eq476

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(X,Y) = Y then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_y_y_pyx_pxy_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
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
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
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
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq61 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X2) = (M.op (M.op (M.op X0 X3) X3) (M.op (M.op (M.op X0 X1) X2) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op (M.op X0 X1) X2) X2) X0 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 (M.op X0 X1) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X1) X0
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 : G, (k (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq74 : ∀ X0 X1 : G, (σ (τ X0)) = (k (σ (M.op (τ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 (M.op (τ X0) X1)
       have i₂ := eq71 (τ X0) X1
       grind)
    | exact superpose eq71 eq18
    | exact resolve eq18 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (τ (σ X0)) = (k (τ (M.op (σ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (σ X0) X1) X0
       have i₂ := eq71 (σ X0) X1
       grind)
    | exact superpose eq71 eq22
    | exact resolve eq22 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : ∀ X0 X1 : G, (k (τ (M.op (σ X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq75 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq75
    | exact resolve eq75 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq77 : ∀ X0 X1 : G, (k (σ (M.op (τ X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq74 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq74
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq590 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op (M.op (M.op X0 X1) X2) X2) = (M.op X0 (M.op (M.op (M.op X0 X1) X2) X2)) ∨ (M.op X0 (M.op (M.op (M.op X0 X1) X2) X2)) = (k (M.op (M.op (M.op X0 X1) X2) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op (M.op (M.op X0 X1) X2) X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 (M.op (M.op (M.op X0 X1) X2) X2) X0
       grind)
    | (have r₁ := eq13 (M.op (M.op (M.op X0 X1) X2) X2) X0
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq593 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op (M.op X0 X1) X0) = X0 ∨ (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X0 X1)
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq13
    | (have j0 := eq13 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X0 X1)
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq594 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq593 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq593
  have eq597 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op (M.op X0 X1) X2) X2)) = (k (M.op (M.op (M.op X0 X1) X2) X2) X0) ∨ (M.op (M.op (M.op X0 X1) X2) X2) = (M.op X0 (M.op (M.op (M.op X0 X1) X2) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq590 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq590
  have eq600 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq612 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (M.op X0 (σ X1))) ∨ (σ X1) = (M.op X0 (σ X1)) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq22 X0 X1
       have i₂ := eq14 X0 (σ X1)
       grind)
    | exact superpose eq14 eq22
    | (have j1 := eq14 X0 (σ X1)
       grind)
    | exact resolve eq22 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq617 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 (τ X1)) ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq624 : ∀ X0 X1 : G, (M.op (σ (M.op (τ X0) X1)) X0) = X0 ∨ (M.op (σ (M.op (τ X0) X1)) X0) = X0 ∨ (σ (M.op (τ X0) X1)) = (M.op X0 (σ (M.op (τ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X1
       have i₂ := eq14 (σ (M.op (τ X0) X1)) X0
       grind)
    | exact superpose eq14 eq77
    | (have j1 := eq14 (σ (M.op (τ X0) X1)) X0
       grind)
    | exact resolve eq77 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq635 : ∀ X0 X1 : G, (M.op (τ (M.op (σ X0) X1)) X0) = X0 ∨ (M.op (τ (M.op (σ X0) X1)) X0) = X0 ∨ (τ (M.op (σ X0) X1)) = (M.op X0 (τ (M.op (σ X0) X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq14 (τ (M.op (σ X0) X1)) X0
       grind)
    | exact superpose eq14 eq76
    | (have j1 := eq14 (τ (M.op (σ X0) X1)) X0
       grind)
    | exact resolve eq76 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq644 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (M.op X0 (τ (M.op (σ X0) X1))) ∨ (M.op (τ (M.op (σ X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq635 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq647 : ∀ X0 X1 : G, (σ (M.op (τ X0) X1)) = (M.op X0 (σ (M.op (τ X0) X1))) ∨ (M.op (σ (M.op (τ X0) X1)) X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq624 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624
  have eq905 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X3) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X2) X4) X4) (M.op (M.op X0 X3) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq61 (M.op (M.op (M.op X0 X1) X2) X2) X0 X2 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq61
    | exact resolve eq61 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq1525 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq600 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq600
    | (have j0 := eq600 X0 X1
       have j1 := eq14 (σ X0) (σ X1)
       grind)
    | exact resolve eq600 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1529 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq600 (M.op X0 X1) X0
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq600
    | (have j0 := eq600 (M.op X0 X1) X0
       grind)
    | exact resolve eq600 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1603 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1529 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529
  have eq9617 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (M.op (σ (M.op X0 X1)) (σ X0)) = (k (σ X0) (σ (M.op X0 X1))) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) (σ (M.op X0 X1))
       have i₂ := eq1603 X0 X1
       grind)
    | exact superpose eq1603 eq13
    | (have j0 := eq13 (σ X0) (σ (M.op X0 X1))
       have j1 := eq1603 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ (M.op X0 X1))
       have r₂ := eq1603 X0 X1
       grind)
    | (have r₁ := eq13 (σ (M.op X0 X1)) (σ X0)
       have r₂ := eq1603 X0 X1
       grind)
    | exact resolve eq13 eq1603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1603
  have eq9642 : ∀ X0 X1 : G, (σ (M.op X0 X1)) ≠ (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (M.op (σ (M.op X0 X1)) (σ X0)) = (k (σ X0) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq9617 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9617
  have eq9643 : ∀ X0 X1 : G, (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (M.op (σ (M.op X0 X1)) (σ X0)) = (k (σ X0) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq9642 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9642
  have eq9647 : ∀ X0 X1 : G, (σ (k X0 (M.op X0 X1))) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9643 X0 X1
       have i₂ := eq15 X0 (M.op X0 X1)
       grind)
    | exact superpose eq15 eq9643
    | (have j0 := eq9643 X0 X1
       grind)
    | exact resolve eq9643 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9643
  have eq10874 : ∀ X0 X1 : G, (k (k (σ (τ X0)) X1) X0) = X0 ∨ (τ X1) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 (τ X1)
       have i₂ := eq617 (τ X0) X1
       grind)
    | exact superpose eq617 eq77
    | (have j1 := eq617 (τ X0) X1
       grind)
    | exact resolve eq77 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq10982 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X0) (τ X1)) ∨ (k (k X0 X1) X0) = X0 ∨ (τ X0) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10874 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq10874
    | (have j0 := eq10874 X0 X1
       grind)
    | exact resolve eq10874 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10874
  have eq11843 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X2) = (M.op (M.op X0 X1) (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq905 X0 X1 (M.op X0 X1) X2 (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq905
    | exact resolve eq905 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq11984 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11843 (M.op (M.op X0 X1) X0) X1 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq11843
    | exact resolve eq11843 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12134 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (M.op (τ X0) X1)) X0) X2) X0) = X0 ∨ (M.op (σ (M.op (τ X0) X1)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11984 X0 (σ (M.op (τ X0) X1)) X2
       have i₂ := eq647 X0 X1
       grind)
    | exact superpose eq647 eq11984
    | (have j1 := eq647 X0 X1
       grind)
    | exact resolve eq11984 eq647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11984
  have eq17950 : ∀ X0 X1 : G, (k (k (τ (σ X0)) X1) X0) = X0 ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 (σ X1)
       have i₂ := eq612 (σ X0) X1
       grind)
    | exact superpose eq612 eq76
    | (have j1 := eq612 (σ X0) X1
       grind)
    | exact resolve eq76 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq18021 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (k X0 X1) X0) = X0 ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq17950 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq17950
    | (have j0 := eq17950 X0 X1
       grind)
    | exact resolve eq17950 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17950
  have eq19722 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = X1 ∨ (k (k X1 X0) X1) = X1 ∨ (τ X1) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X1 (τ X0)
       have i₂ := eq10982 X1 X0
       grind)
    | exact superpose eq10982 eq77
    | (have j1 := eq10982 X1 X0
       grind)
    | exact resolve eq77 eq10982
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq10982
  have eq19876 : ∀ X0 X1 : G, (τ X1) = (M.op (τ X0) (τ X1)) ∨ (k (k X1 X0) X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19722 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19722
    | (have j0 := eq19722 X0 X1
       grind)
    | exact resolve eq19722 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19722
  have eq36828 : ∀ X0 X1 : G, (σ (τ X0)) = (M.op X1 (σ (τ X0))) ∨ (M.op (σ (τ X0)) X1) = X1 ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq647 X0 (τ X1)
       have i₂ := eq19876 X0 X1
       grind)
    | exact superpose eq19876 eq647
    | (have j1 := eq19876 X1 X0
       grind)
    | exact resolve eq647 eq19876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq36834 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (σ (τ X0)) X1) X2) X1) = X1 ∨ (M.op (σ (τ X0)) X1) = X1 ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12134 X0 (τ X1) X2
       have i₂ := eq19876 X0 X1
       grind)
    | exact superpose eq19876 eq12134
    | (have j1 := eq19876 X1 X0
       grind)
    | exact resolve eq12134 eq19876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12134 eq19876
  have eq37025 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X1) = X1 ∨ (M.op (σ (τ X0)) X1) = X1 ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq36834 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq36834
    | (have j0 := eq36834 X0 X1 X2
       grind)
    | exact resolve eq36834 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36834
  have eq37027 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op (σ (τ X0)) X1) = X1 ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq36828 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq36828
    | (have j0 := eq36828 X0 X1
       grind)
    | exact resolve eq36828 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36828
  have eq37051 : ∀ X0 X1 X2 : G, (M.op X0 X1) = X1 ∨ (M.op (M.op (M.op X0 X1) X2) X1) = X1 ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq37025 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37025
    | (have j0 := eq37025 X0 X1 X2
       grind)
    | exact resolve eq37025 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37025
  have eq37053 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq37027 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq37027
    | (have j0 := eq37027 X0 X1
       grind)
    | exact resolve eq37027 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37027
  have eq37062 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) X2) X1) = X1 ∨ (k (k X0 X1) X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq37051 X0 X1 X2
       have j1 := eq12 (k X0 X1) X0
       grind)
    | (have r₁ := eq37051 X1 X0 X2
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq37051 X0 X0 X2
       have r₂ := eq12 X0 (M.op (M.op X0 X0) X2)
       grind)
    | exact resolve eq37051 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37051
  have eq37064 : ∀ X0 X1 : G, (k (k X0 X1) X0) = X0 ∨ (M.op X1 X0) = X0 ∨ (k X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq37053 X0 X1
       have j1 := eq12 (k X0 X1) X0
       grind)
    | (have r₁ := eq37053 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq37053 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37053 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37053
  have eq81044 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1525 x y
       grind)
    | exact superpose eq1525 eq16
    | (have j1 := eq1525 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1525 x y
       grind)
    | exact resolve eq16 eq1525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1525
  have eq81284 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq81044
  have eq81403 : ∀ X0 X1 : G, (σ (k X0 (M.op X0 X1))) = (M.op (σ (M.op X0 X1)) (σ X0)) ∨ (σ X0) = (M.op (σ (M.op X0 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq9647 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9647
  have eq86402 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (k (k X1 X0) X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq597 X0 X1 X1
       have i₂ := eq37062 X0 X1 X1
       grind)
    | exact superpose eq37062 eq597
    | (have j1 := eq37062 X1 X0 x
       grind)
    | exact resolve eq597 eq37062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq597 eq37062
  have eq86741 : ∀ X0 X1 : G, (k (k X1 X0) X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq86402 X0 X1
       have j1 := eq12 (k X1 X0) X1
       grind)
    | (have r₁ := eq86402 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq86402 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86402
  have eq86793 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 (M.op X0 X1)) ∨ (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq86741 X0 (M.op X0 X1)
       have i₂ := eq71 X0 X1
       grind)
    | exact superpose eq71 eq86741
    | (have j0 := eq86741 X0 (M.op X0 X1)
       grind)
    | exact resolve eq86741 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq87106 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) ∨ (M.op X0 X1) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq86793 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86793
  have eq108392 : ∀ X0 X1 : G, (k (τ (σ X0)) X1) = X1 ∨ (k (k X1 X0) X1) = X1 ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X1 (σ X0)
       have i₂ := eq18021 X1 X0
       grind)
    | exact superpose eq18021 eq76
    | (have j1 := eq18021 X1 X0
       grind)
    | exact resolve eq76 eq18021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18021
  have eq108605 : ∀ X0 X1 : G, (σ X1) = (M.op (σ X0) (σ X1)) ∨ (k (k X1 X0) X1) = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq108392 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq108392
    | (have j0 := eq108392 X0 X1
       grind)
    | exact resolve eq108392 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108392
  have eq108656 : (σ (M.op x y)) ≠ (σ y) ∨ y = (k (k y x) y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq108605 x y
       grind)
    | exact superpose eq108605 eq16
    | (have j1 := eq108605 x y
       grind)
    | exact resolve eq16 eq108605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108605
  have eq108867 : (σ y) ≠ (σ y) ∨ y = (k (k y x) y) ∨ y = (k x y) := by
    first
    | exact superpose eq37064 eq108656
    | (have j1 := eq37064 y x
       grind)
    | exact resolve eq108656 eq37064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37064 eq108656
  have eq108868 : y = (k (k y x) y) ∨ y = (k x y) := by grind
  clear eq108867
  have eq122110 : x = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq76 x (σ y)
       have i₂ := eq81284
       grind)
    | exact superpose eq81284 eq76
    | exact resolve eq76 eq81284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81284
  have eq122293 : x = (k y x) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq122110
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq122110
    | exact resolve eq122110 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122110
  have eq122318 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq122293
       have r₂ := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq122293
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq122293
       have r₂ := eq12 x y
       grind)
    | exact resolve eq122293 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122293
  have eq122338 : y = (k (τ (σ x)) y) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq76 y (σ x)
       have i₂ := eq122318
       grind)
    | exact superpose eq122318 eq76
    | exact resolve eq76 eq122318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122339 : (τ (σ x)) = (M.op y (τ (σ x))) ∨ y = (M.op (τ (σ x)) y) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq644 y (σ x)
       have i₂ := eq122318
       grind)
    | exact superpose eq122318 eq644
    | exact resolve eq644 eq122318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq644 eq122318
  have eq122519 : x = (M.op y x) ∨ y = (M.op (τ (σ x)) y) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq122339
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq122339
    | exact resolve eq122339 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122339
  have eq122520 : x = (M.op y x) ∨ y = (M.op (τ (σ x)) y) ∨ x = (k y x) := by grind
  clear eq122519
  have eq122521 : y = (k x y) ∨ x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq122338
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq122338
    | exact resolve eq122338 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122338
  have eq122538 : y = (M.op x y) ∨ x = (M.op y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq122520
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq122520
    | exact resolve eq122520 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122520
  have eq122539 : y = (k x y) ∨ x = (k y x) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq122521
       have r₂ := eq12 x y
       grind)
    | exact resolve eq122521 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122521
  have eq122547 : x = (k y x) ∨ x = (M.op y x) := by
    first
    | (have j1 := eq12 y x
       grind)
    | (have r₁ := eq122538
       have r₂ := eq12 y x
       grind)
    | (have r₁ := eq122538
       have r₂ := eq12 x y
       grind)
    | exact resolve eq122538 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122538
  have eq122551 : y = (k x y) ∨ y = (k x y) := by
    first
    | exact superpose eq122539 eq108868
    | exact resolve eq108868 eq122539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108868
  have eq122557 : x = (k y x) ∨ (M.op x y) = (k y x) ∨ x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq86741 y x
       have i₂ := eq122539
       grind)
    | exact superpose eq122539 eq86741
    | (have j0 := eq86741 y x
       grind)
    | exact resolve eq86741 eq122539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86741 eq122539
  have eq122560 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
  clear eq122557
  have eq122566 : y = (k x y) := by grind
  clear eq122551
  have eq122577 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq600 x y
       have i₂ := eq122566
       grind)
    | exact superpose eq122566 eq600
    | (have j0 := eq600 x y
       grind)
    | exact resolve eq600 eq122566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq600
  have eq122586 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq122577
  have eq122590 : x = (M.op y x) ∨ x = (M.op y x) ∨ y = (M.op x y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq14 y x
       have i₂ := eq122547
       grind)
    | exact superpose eq122547 eq14
    | (have j0 := eq14 y x
       grind)
    | exact resolve eq14 eq122547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122547
  have eq122601 : y = (M.op x y) ∨ x = (M.op y x) := by grind
  clear eq122590
  have eq122603 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq122586
  have eq122604 : ∀ X0 : G, x = (M.op (M.op (M.op y X0) X0) x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq122601
       grind)
    | exact superpose eq122601 eq9
    | exact resolve eq9 eq122601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq122616 : (M.op y x) = (k x y) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq594 x y
       have i₂ := eq122601
       grind)
    | exact superpose eq122601 eq594
    | exact resolve eq594 eq122601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122601
  have eq122749 : (M.op y x) = (k x y) ∨ x = (M.op y x) := by grind
  clear eq122616
  have eq122755 : y = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq122749
       have i₂ := eq122566
       grind)
    | exact superpose eq122566 eq122749
    | exact resolve eq122749 eq122566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122749
  have eq122819 : ∀ X0 : G, (M.op y x) = (M.op (M.op y X0) (M.op y x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq11843 y x x
       have i₂ := eq122755
       grind)
    | exact superpose eq122755 eq11843
    | exact resolve eq11843 eq122755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11843
  have eq122925 : ∀ X0 : G, y = (M.op (M.op y X0) y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq122755 eq122819
    | exact resolve eq122819 eq122755
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122755 eq122819
  have eq123277 : x ≠ (M.op x y) ∨ x = (k y x) := by grind
  have eq124389 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq122604 y
       have i₂ := eq122925 y
       grind)
    | exact superpose eq122925 eq122604
    | exact resolve eq122604 eq122925
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122604 eq122925
  have eq124692 : x = (M.op y x) := by grind
  clear eq124389
  have eq124743 : x = (M.op y x) := by grind
  clear eq124692
  have eq124825 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) X0) y) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq124743
       grind)
    | exact superpose eq124743 eq9
    | exact resolve eq9 eq124743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124837 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq594 y x
       have i₂ := eq124743
       grind)
    | exact superpose eq124743 eq594
    | exact resolve eq594 eq124743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq124954 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq81403 y x
       have i₂ := eq124743
       grind)
    | exact superpose eq124743 eq81403
    | exact resolve eq81403 eq124743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124743
  have eq131641 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq122603
       grind)
    | exact superpose eq122603 eq16
    | exact resolve eq16 eq122603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq131644 : x = (k (τ (σ y)) x) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq76 x (σ y)
       have i₂ := eq122603
       grind)
    | exact superpose eq122603 eq76
    | exact resolve eq76 eq122603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq122603
  have eq131831 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq131644
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq131644
    | exact resolve eq131644 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131644
  have eq132014 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq87106 (σ y) (σ x)
       have i₂ := eq131831
       grind)
    | exact superpose eq131831 eq87106
    | exact resolve eq87106 eq131831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87106 eq131831
  have eq132038 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq132014
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq132014
    | exact resolve eq132014 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132014
  have eq132060 : (σ x) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq132038
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq132038
    | exact resolve eq132038 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132038
  have eq132069 : (σ (M.op x y)) = (σ x) ∨ (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (k y x) := by
    first
    | exact superpose eq122560 eq132060
    | exact resolve eq132060 eq122560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132060
  have eq132076 : (σ (M.op x y)) = (σ x) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (k y x) := by
    first
    | exact superpose eq122560 eq132069
    | exact resolve eq132069 eq122560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122560 eq132069
  have eq132078 : (σ (M.op x y)) = (σ x) ∨ x = (k y x) := by
    first
    | (have r₁ := eq132076
       have r₂ := eq16
       grind)
    | exact resolve eq132076 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132076
  have eq132080 : (M.op x y) = (τ (σ x)) ∨ x = (k y x) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq132078
       grind)
    | exact superpose eq132078 eq10
    | exact resolve eq10 eq132078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132078
  have eq132265 : x = (M.op x y) ∨ x = (k y x) := by
    first
    | (have i₁ := eq132080
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq132080
    | exact resolve eq132080 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132080
  have eq132266 : x = (k y x) := by
    first
    | (have r₁ := eq132265
       have r₂ := eq123277
       grind)
    | exact resolve eq132265 eq123277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123277 eq132265
  have eq132267 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq124837
       have i₂ := eq132266
       grind)
    | exact superpose eq132266 eq124837
    | exact resolve eq124837 eq132266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124837
  have eq135102 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq131641
       have i₂ := eq132267
       grind)
    | exact superpose eq132267 eq131641
    | exact resolve eq131641 eq132267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131641
  have eq135103 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq135102
  have eq135121 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) X0) X0) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 (σ y) (σ x) X0
       have i₂ := eq135103
       grind)
    | exact superpose eq135103 eq9
    | exact resolve eq9 eq135103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135103
  have eq151833 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq124954
       have i₂ := eq132266
       grind)
    | exact superpose eq132266 eq124954
    | exact resolve eq124954 eq132266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124954 eq132266
  have eq151835 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq151833
       grind)
    | exact superpose eq151833 eq16
    | exact resolve eq16 eq151833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151833
  have eq152074 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq151835
       have i₂ := eq132267
       grind)
    | exact superpose eq132267 eq151835
    | exact resolve eq151835 eq132267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq151835
  have eq152075 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq152074
  have eq152083 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq152075
       grind)
    | exact superpose eq152075 eq16
    | exact resolve eq16 eq152075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152093 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq135121 (σ y)
       have i₂ := eq152075
       grind)
    | exact superpose eq152075 eq135121
    | exact resolve eq135121 eq152075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135121
  have eq152275 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq152093
  have eq152335 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq152075 eq152275
    | exact resolve eq152275 eq152075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152275
  have eq152342 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq132267 eq152083
    | exact resolve eq152083 eq132267
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132267 eq152083
  have eq152366 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq152075 eq152335
    | exact resolve eq152335 eq152075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152075 eq152335
  have eq152380 : x = (M.op x y) := by
    first
    | (have r₁ := eq152366
       have r₂ := eq152342
       grind)
    | exact resolve eq152366 eq152342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152342 eq152366
  have eq152392 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq152380
       grind)
    | exact superpose eq152380 eq16
    | exact resolve eq16 eq152380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152408 : y = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq124825 y
       have i₂ := eq152380
       grind)
    | exact superpose eq152380 eq124825
    | exact resolve eq124825 eq152380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124825
  have eq152624 : y = (M.op x y) := by
    first
    | (have i₁ := eq152408
       have i₂ := eq152380
       grind)
    | exact superpose eq152380 eq152408
    | exact resolve eq152408 eq152380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152408
  have eq152633 : x = y := by
    first
    | (have i₁ := eq152624
       have i₂ := eq152380
       grind)
    | exact superpose eq152380 eq152624
    | exact resolve eq152624 eq152380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152380 eq152624
  have eq152638 : x = (k x x) := by
    first
    | (have i₁ := eq122566
       have i₂ := eq152633
       grind)
    | exact superpose eq152633 eq122566
    | exact resolve eq122566 eq152633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122566
  have eq152783 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq14 x x
       have i₂ := eq152638
       grind)
    | exact superpose eq152638 eq14
    | (have j0 := eq14 x x
       grind)
    | exact resolve eq14 eq152638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq152786 : x = (M.op x x) := by grind
  clear eq152783
  have eq152974 : (M.op (σ x) (σ x)) = (σ (k x x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq81403 x x
       have i₂ := eq152786
       grind)
    | exact superpose eq152786 eq81403
    | exact resolve eq81403 eq152786
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81403 eq152786
  have eq153007 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq152974
       have i₂ := eq152638
       grind)
    | exact superpose eq152638 eq152974
    | exact resolve eq152974 eq152638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152638 eq152974
  have eq153008 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq153007
  have eq153099 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq152392
       have i₂ := eq152633
       grind)
    | exact superpose eq152633 eq152392
    | exact resolve eq152392 eq152633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152392 eq152633
  have eq153100 : False := by grind
  exact eq153100

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pyx_pyy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq17
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
  have eq63 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq63 X0 X1
       grind)
    | exact superpose eq63 eq12
    | (have r₁ := eq12 (M.op X0 X1) X0
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq75 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (k (τ (M.op (σ X0) X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq22 (M.op (σ X0) X1) X0
       have i₂ := eq70 (σ X0) X1
       grind)
    | exact superpose eq70 eq22
    | exact resolve eq22 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq637 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq637 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq637
    | (have j0 := eq637 (σ X0) (σ X1)
       grind)
    | exact resolve eq637 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq648 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq637 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq637
    | (have j0 := eq637 (τ X0) (τ X1)
       grind)
    | exact resolve eq637 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq649 : ∀ X0 X1 : G, (τ (M.op (σ X0) X1)) = (M.op X0 (τ (M.op (σ X0) X1))) ∨ (M.op X0 (τ (M.op (σ X0) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq637 (τ (M.op (σ X0) X1)) X0
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq637
    | (have j0 := eq637 (τ (M.op (σ X0) X1)) X0
       grind)
    | exact resolve eq637 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq880 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq646 X1 X0
       have i₂ := eq637 X1 X0
       grind)
    | exact superpose eq637 eq646
    | (have j0 := eq646 X1 X0
       have j1 := eq637 (σ X1) (σ X0)
       grind)
    | exact resolve eq646 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq887 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ (M.op X0 X1))) ∨ (σ X0) = (M.op (σ X0) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq646 (M.op X0 X1) X0
       have i₂ := eq70 X0 X1
       grind)
    | exact superpose eq70 eq646
    | (have j0 := eq646 (M.op X0 X1) X0
       grind)
    | exact resolve eq646 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq646
  have eq1632 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X1 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq648 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq648
  have eq1657 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1632 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1632
    | (have j0 := eq1632 (σ X1) (σ X0)
       grind)
    | exact resolve eq1632 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1632
  have eq1675 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1657 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1657
    | (have j0 := eq1657 X0 X1
       grind)
    | exact resolve eq1657 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1657
  have eq1683 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1675 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq1675
    | (have j0 := eq1675 X0 X1
       grind)
    | exact resolve eq1675 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1675
  have eq1689 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1683 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1683
    | (have j0 := eq1683 X0 X1
       grind)
    | exact resolve eq1683 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1683
  have eq1692 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1689 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1689
    | (have j0 := eq1689 X0 X1
       grind)
    | exact resolve eq1689 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1689
  have eq1707 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1692 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1692
    | (have j0 := eq1692 (σ X0) (σ X1)
       grind)
    | exact resolve eq1692 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1692
  have eq22248 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq880 x y
       grind)
    | exact superpose eq880 eq16
    | (have j1 := eq880 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq880 x y
       grind)
    | exact resolve eq16 eq880
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq880
  have eq22302 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq22248
  have eq22337 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22302
       grind)
    | exact superpose eq22302 eq16
    | exact resolve eq16 eq22302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22341 : (τ (σ x)) = (M.op x (τ (σ x))) ∨ x = (M.op x (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq649 x (σ y)
       have i₂ := eq22302
       grind)
    | exact superpose eq22302 eq649
    | exact resolve eq649 eq22302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq649
  have eq22345 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq22302
       grind)
    | exact superpose eq22302 eq12
    | exact resolve eq12 eq22302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22346 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq22302
       grind)
    | exact superpose eq22302 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq22302
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq22302
       grind)
    | exact resolve eq13 eq22302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22302
  have eq22369 : (σ x) = (σ y) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq22346
  have eq22375 : (M.op (σ x) (σ x)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22369
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq22369
    | exact resolve eq22369 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22369
  have eq22376 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22345
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq22345
    | exact resolve eq22345 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22345
  have eq22380 : x = (M.op x x) ∨ x = (M.op x (τ (σ x))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22341
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22341
    | exact resolve eq22341 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22341
  have eq22383 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq637 eq22375
    | (have j1 := eq637 y x
       grind)
    | exact resolve eq22375 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22375
  have eq22384 : (σ (M.op x y)) = (σ x) ∨ (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq637 eq22376
    | (have j1 := eq637 y x
       grind)
    | exact resolve eq22376 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq637 eq22376
  have eq22387 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq22380
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22380
    | exact resolve eq22380 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22380
  have eq22388 : x = (M.op x y) ∨ x = (M.op x x) := by grind
  clear eq22387
  have eq22389 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22384
       have r₂ := eq22337
       grind)
    | exact resolve eq22384 eq22337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22384
  have eq22700 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq63 x y
       have i₂ := eq22388
       grind)
    | exact superpose eq22388 eq63
    | exact resolve eq63 eq22388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq22388
  have eq22719 : x = (M.op x x) := by grind
  clear eq22700
  have eq22754 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq887 x x
       have i₂ := eq22719
       grind)
    | exact superpose eq22719 eq887
    | exact resolve eq887 eq22719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq22759 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq22754
  have eq107364 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq22383
       have r₂ := eq22389
       grind)
    | exact resolve eq22383 eq22389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22383 eq22389
  have eq107365 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq107364
       have i₂ := eq22759
       grind)
    | exact superpose eq22759 eq107364
    | exact resolve eq107364 eq22759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22759 eq107364
  have eq107366 : x = (M.op x y) := by
    first
    | (have r₁ := eq107365
       have r₂ := eq22337
       grind)
    | exact resolve eq107365 eq22337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22337 eq107365
  have eq107368 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq107366
       grind)
    | exact superpose eq107366 eq16
    | exact resolve eq16 eq107366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107424 : x ≠ y ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq107366
       grind)
    | exact superpose eq107366 eq12
    | exact resolve eq12 eq107366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107425 : x ≠ x ∨ x = y ∨ (k y x) = (M.op x x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq107366
       grind)
    | exact superpose eq107366 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq107366
       grind)
    | exact resolve eq13 eq107366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107366
  have eq107506 : x = y ∨ (k y x) = (M.op x x) := by grind
  clear eq107425
  have eq107543 : x = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq107506
       have i₂ := eq22719
       grind)
    | exact superpose eq22719 eq107506
    | exact resolve eq107506 eq22719
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22719 eq107506
  have eq107608 : x = (k y x) := by
    first
    | (have r₁ := eq107424
       have r₂ := eq107543
       grind)
    | exact resolve eq107424 eq107543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107424 eq107543
  have eq107624 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1707 y x
       have i₂ := eq107608
       grind)
    | exact superpose eq107608 eq1707
    | (have j0 := eq1707 y x
       grind)
    | exact resolve eq1707 eq107608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1707 eq107608
  have eq107653 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq107624
  have eq107660 : False := by grind
  exact eq107660

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_y_pyx_y_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  clear eq17
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
  have eq570 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq578 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq570 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq570
    | (have j0 := eq570 (σ X0) (σ X1)
       grind)
    | exact resolve eq570 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq570 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq570
    | (have j0 := eq570 (τ X0) (τ X1)
       grind)
    | exact resolve eq570 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1010 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq578 X1 X0
       have i₂ := eq570 X1 X0
       grind)
    | exact superpose eq570 eq578
    | (have j0 := eq578 X1 X0
       have j1 := eq570 (σ X1) (σ X0)
       grind)
    | exact resolve eq578 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq1630 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X1 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq580 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580
  have eq1654 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1630 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1630
    | (have j0 := eq1630 (σ X1) (σ X0)
       grind)
    | exact resolve eq1630 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1630
  have eq1672 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1654 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq1654
    | (have j0 := eq1654 X0 X1
       grind)
    | exact resolve eq1654 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1654
  have eq1680 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1672 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq1672
    | (have j0 := eq1672 X0 X1
       grind)
    | exact resolve eq1672 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672
  have eq1686 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1680 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1680
    | (have j0 := eq1680 X0 X1
       grind)
    | exact resolve eq1680 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1680
  have eq1689 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1686 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1686
    | (have j0 := eq1686 X0 X1
       grind)
    | exact resolve eq1686 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1686
  have eq1704 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1689 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1689
    | (have j0 := eq1689 (σ X0) (σ X1)
       grind)
    | exact resolve eq1689 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1689
  have eq19921 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1010 x y
       grind)
    | exact superpose eq1010 eq16
    | (have j1 := eq1010 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq1010 x y
       grind)
    | exact resolve eq16 eq1010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1010
  have eq19969 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq19921
  have eq19997 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19969
       grind)
    | exact superpose eq19969 eq16
    | exact resolve eq16 eq19969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20004 : (σ x) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq19969
       grind)
    | exact superpose eq19969 eq12
    | exact resolve eq12 eq19969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20005 : (σ x) ≠ (σ x) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq19969
       grind)
    | exact superpose eq19969 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq19969
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq19969
       grind)
    | exact resolve eq13 eq19969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19969
  have eq20026 : (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq20005
  have eq20032 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20026
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq20026
    | exact resolve eq20026 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20026
  have eq20033 : (σ x) = (σ (k y x)) ∨ (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq20004
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq20004
    | exact resolve eq20004 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20004
  have eq20039 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq570 eq20032
    | (have j1 := eq570 y x
       grind)
    | exact resolve eq20032 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20032
  have eq20040 : (σ (M.op x y)) = (σ x) ∨ (σ x) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq570 eq20033
    | (have j1 := eq570 y x
       grind)
    | exact resolve eq20033 eq570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570 eq20033
  have eq20044 : x = (M.op x y) := by grind
  clear eq19997 eq20039 eq20040
  have eq20048 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq20044
       grind)
    | exact superpose eq20044 eq16
    | exact resolve eq16 eq20044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20050 : x ≠ y ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq20044
       grind)
    | exact superpose eq20044 eq12
    | exact resolve eq12 eq20044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20051 : x ≠ x ∨ x = y ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq20044
       grind)
    | exact superpose eq20044 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20044
       grind)
    | exact resolve eq13 eq20044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20044
  have eq20072 : x = y ∨ x = (k y x) := by grind
  clear eq20051
  have eq20075 : x = (k y x) := by
    first
    | (have r₁ := eq20050
       have r₂ := eq20072
       grind)
    | exact resolve eq20050 eq20072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20050 eq20072
  have eq20156 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1704 y x
       have i₂ := eq20075
       grind)
    | exact superpose eq20075 eq1704
    | (have j0 := eq1704 y x
       grind)
    | exact resolve eq1704 eq20075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1704 eq20075
  have eq20185 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq20156
  have eq20192 : False := by grind
  exact eq20192

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_x_pyx_pxy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X0) = X0 := by
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
  have eq20 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X2) = (M.op (M.op (M.op X0 X3) X3) (M.op (M.op (M.op X0 X1) X2) X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op (M.op (M.op X0 X1) X2) X2) X0 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X0) (M.op (M.op X0 X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) X2) X2 X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq22 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X0 X1) X0 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq31 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op (M.op X0 X1) X2) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have r₁ := eq12 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq22 X0 X1
       grind)
    | exact superpose eq22 eq12
    | (have r₁ := eq12 (M.op X0 X1) X0
       have r₂ := eq22 X0 X1
       grind)
    | exact resolve eq12 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq34 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X0 X1) X2) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq31 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq43 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq48 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) (τ X0)) = X1 ∨ (M.op (τ X0) X1) = X1 := by
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
  have eq50 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq54 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq30 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq30
    | exact resolve eq30 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (τ (k (k (σ X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 (k X0 (τ X1)) X2
       have i₂ := eq19 X1 X0
       grind)
    | exact superpose eq19 eq43
    | exact resolve eq43 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq101 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (M.op (M.op (M.op (τ X0) X1) X2) X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (M.op (M.op (M.op (τ X0) X1) X2) X2)
       have i₂ := eq34 (τ X0) X1 X2
       grind)
    | exact superpose eq34 eq18
    | exact resolve eq18 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 X1 X2 : G, (k X0 (σ (M.op (M.op (M.op (τ X0) X1) X2) X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq101 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq101
    | exact resolve eq101 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq132 : ∀ X0 X1 X2 : G, (σ (τ X0)) = (k X0 (σ (σ (M.op (M.op (M.op (τ (τ X0)) X1) X2) X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq18 X0 (σ (M.op (M.op (M.op (τ (τ X0)) X1) X2) X2))
       have i₂ := eq104 (τ X0) X1 X2
       grind)
    | exact superpose eq104 eq18
    | exact resolve eq18 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (M.op (M.op (M.op (τ (τ X0)) X1) X2) X2)))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq132 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq132
    | exact resolve eq132 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq188 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X3) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X2) X4) X4) (M.op (M.op X0 X3) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op (M.op X0 X3) X3) (M.op (M.op (M.op X0 X1) X2) X2) X4
       have i₂ := eq20 X0 X1 X2 X3
       grind)
    | exact superpose eq20 eq9
    | exact resolve eq9 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq240 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (M.op (σ X2) (k X0 (σ X1))) ∨ (k X0 (σ X1)) = (M.op (σ X2) (σ X2)) ∨ (k X0 (σ X1)) = (M.op (σ X2) (k X0 (σ X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 X0 (k (τ X0) X1)
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq50
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X1) X2) = (M.op (σ (k X0 X0)) (M.op (M.op (σ X0) X1) X2)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq21 (σ X0) X1 X2
       have i₂ := eq50 X0 X0
       grind)
    | exact superpose eq50 eq21
    | (have j1 := eq50 X0 X0
       grind)
    | exact resolve eq21 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq50
  have eq259 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X0) X1) X2) = (M.op (σ (k X0 X0)) (M.op (M.op (σ X0) X1) X2)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq253 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq911 : ∀ X0 X1 X2 : G, (τ (k (k (σ X0) X1) X2)) = (k (M.op (τ X1) X0) (τ X2)) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq43 (M.op (τ X1) X0) X2
       have i₂ := eq48 X1 X0
       grind)
    | exact superpose eq48 eq43
    | (have j1 := eq48 X1 X0
       grind)
    | exact resolve eq43 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq48
  have eq920 : ∀ X0 X1 X2 : G, (k (k X0 (τ X1)) (τ X2)) = (k (M.op (τ X1) X0) (τ X2)) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq911 X0 X1 X2
       have i₂ := eq66 X0 X1 X2
       grind)
    | exact superpose eq66 eq911
    | (have j0 := eq911 X0 X1 X2
       grind)
    | exact resolve eq911 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq911
  have eq1951 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X2) = (M.op (M.op X0 X1) (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq188 X0 X1 (M.op X0 X1) X2 (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq188
    | exact resolve eq188 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188
  have eq2044 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1951 (M.op (M.op X0 X1) X0) X1 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq1951
    | exact resolve eq1951 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1951
  have eq3114 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (σ (k (τ X0) (τ X0))) (M.op (M.op X0 X1) X2)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq259 (τ X0) X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq259
    | exact resolve eq259 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq3176 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (k (σ (τ X0)) X0) (M.op (M.op X0 X1) X2)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3114 X0 X1 X2
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq3114
    | (have j0 := eq3114 X0 X1 X2
       grind)
    | exact resolve eq3114 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq3114
  have eq3181 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (k X0 X0) (M.op (M.op X0 X1) X2)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3176 X0 X1 X2
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq3176
    | (have j0 := eq3176 X0 X1 X2
       grind)
    | exact resolve eq3176 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3176
  have eq14875 : ∀ X0 X1 X2 X3 : G, (k X0 X0) = (k (k X0 X0) (M.op (M.op (M.op (M.op X0 X1) X2) X3) X3)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq34 (k X0 X0) (M.op (M.op X0 X1) X2) X3
       have i₂ := eq3181 X0 X1 X2
       grind)
    | exact superpose eq3181 eq34
    | (have j1 := eq3181 X0 X1 X2
       grind)
    | exact resolve eq34 eq3181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq3181
  have eq33217 : ∀ X0 : G, (k X0 X0) = (k (k X0 X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq14875 X0 x X0 X0
       have i₂ := eq2044 X0 x X0
       grind)
    | exact superpose eq2044 eq14875
    | (have j0 := eq14875 X0 x x x
       grind)
    | exact resolve eq14875 eq2044
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2044 eq14875
  have eq47629 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq33217 (τ X0)
       have i₂ := eq920 (τ X0) X0 X0
       grind)
    | exact superpose eq920 eq33217
    | (have j0 := eq33217 (τ X0)
       have j1 := eq920 (τ X0) X0 x
       grind)
    | exact resolve eq33217 eq920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq920 eq33217
  have eq47742 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (k (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq47629 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47629
  have eq47820 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq47742 X0
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq47742
    | (have j0 := eq47742 X0
       grind)
    | exact resolve eq47742 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47742
  have eq47903 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq47820 X0
       have i₂ := eq33 (τ X0) (τ X0)
       grind)
    | exact superpose eq33 eq47820
    | (have j0 := eq47820 X0
       grind)
    | exact resolve eq47820 eq33
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47820
  have eq47961 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (τ (k (σ X0) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq47903 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq47903
    | exact resolve eq47903 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48034 : ∀ X0 : G, (τ X0) = (k (τ X0) (τ X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 (τ X0) (τ X0)
       have i₂ := eq47903 X0
       grind)
    | exact superpose eq47903 eq33
    | (have j1 := eq47903 X0
       grind)
    | exact resolve eq33 eq47903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq48144 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq47903 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47903
  have eq48148 : ∀ X0 : G, (τ X0) = (τ (k X0 X0)) ∨ (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48034 X0
       have i₂ := eq54 X0 X0
       grind)
    | exact superpose eq54 eq48034
    | (have j0 := eq48034 X0
       grind)
    | exact resolve eq48034 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq48034
  have eq48166 : ∀ X0 : G, (M.op X0 X0) = (k (τ (σ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq47961 X0
       have i₂ := eq30 (σ X0) X0
       grind)
    | exact superpose eq30 eq47961
    | (have j0 := eq47961 X0
       grind)
    | exact resolve eq47961 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq47961
  have eq48167 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq48148 X0
       have j1 := eq48144 X0
       grind)
    | (have r₁ := eq48148 X0
       have r₂ := eq48144 X0
       grind)
    | exact resolve eq48148 eq48144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48144 eq48148
  have eq48179 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq48166 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq48166
    | (have j0 := eq48166 X0
       grind)
    | exact resolve eq48166 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48166
  have eq48186 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq48179 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq48179 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq48179 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48179
  have eq48319 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq48186 (σ X0)
       grind)
    | exact superpose eq48186 eq15
    | exact resolve eq15 eq48186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48423 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq48319 X0
       have i₂ := eq48186 X0
       grind)
    | exact superpose eq48186 eq48319
    | exact resolve eq48319 eq48186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48319
  have eq49102 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op (τ (k X0 X0)) X1) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0 (τ X0) X1
       have i₂ := eq48167 X0
       grind)
    | exact superpose eq48167 eq104
    | exact resolve eq104 eq48167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq49111 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op (M.op (τ (k (τ X0) (τ X0))) X1) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq135 X0 (τ (τ X0)) X1
       have i₂ := eq48167 (τ X0)
       grind)
    | exact superpose eq48167 eq135
    | exact resolve eq135 eq48167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq49423 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq49111 X0 X1
       have i₂ := eq48186 (τ X0)
       grind)
    | exact superpose eq48186 eq49111
    | exact resolve eq49111 eq48186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49111
  have eq49432 : ∀ X0 X1 : G, (k X0 (σ (M.op (M.op (τ (M.op X0 X0)) X1) X1))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq49102 X0 X1
       have i₂ := eq48186 X0
       grind)
    | exact superpose eq48186 eq49102
    | exact resolve eq49102 eq48186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49102
  have eq49482 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op (M.op (τ (τ (k X0 X0))) X1) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq49423 X0 X1
       have i₂ := eq48167 X0
       grind)
    | exact superpose eq48167 eq49423
    | exact resolve eq49423 eq48167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49423
  have eq49525 : ∀ X0 X1 : G, (k X0 (σ (σ (M.op (M.op (τ (τ (M.op X0 X0))) X1) X1)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq49482 X0 X1
       have i₂ := eq48186 X0
       grind)
    | exact superpose eq48186 eq49482
    | exact resolve eq49482 eq48186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49482
  have eq49695 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq22 (σ X0) (σ X0)
       have i₂ := eq48423 X0
       grind)
    | exact superpose eq48423 eq22
    | exact resolve eq22 eq48423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52595 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = (M.op (σ X2) (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1))))) ∨ (M.op (σ X2) (σ X2)) = (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1)))) ∨ (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1)))) = (M.op (σ X2) (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq240 X0 (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1)) X2
       have i₂ := eq49432 (τ X0) X1
       grind)
    | exact superpose eq49432 eq240
    | (have j0 := eq240 X0 (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1)) X2
       grind)
    | exact resolve eq240 eq49432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq49432
  have eq52665 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = (M.op (σ X2) (k X0 (σ (σ (M.op (M.op (τ (τ (k X0 X0))) X1) X1))))) ∨ (M.op (σ X2) (σ X2)) = (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1)))) ∨ (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1)))) = (M.op (σ X2) (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52595 X0 X1 X2
       have i₂ := eq48167 X0
       grind)
    | exact superpose eq48167 eq52595
    | (have j0 := eq52595 X0 X1 X2
       grind)
    | exact resolve eq52595 eq48167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52595
  have eq52761 : ∀ X0 X1 X2 : G, (σ (k (τ X0) X2)) = (M.op (σ X2) (k X0 (σ (σ (M.op (M.op (τ (τ (M.op X0 X0))) X1) X1))))) ∨ (M.op (σ X2) (σ X2)) = (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1)))) ∨ (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1)))) = (M.op (σ X2) (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52665 X0 X1 X2
       have i₂ := eq48186 X0
       grind)
    | exact superpose eq48186 eq52665
    | (have j0 := eq52665 X0 X1 X2
       grind)
    | exact resolve eq52665 eq48186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52665
  have eq52830 : ∀ X0 X1 X2 : G, (M.op (σ X2) X0) = (σ (k (τ X0) X2)) ∨ (M.op (σ X2) (σ X2)) = (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1)))) ∨ (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1)))) = (M.op (σ X2) (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52761 X0 X1 X2
       have i₂ := eq49525 X0 X1
       grind)
    | exact superpose eq49525 eq52761
    | (have j0 := eq52761 X0 X1 X2
       grind)
    | exact resolve eq52761 eq49525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52761
  have eq52875 : ∀ X0 X1 X2 : G, (M.op (σ X2) X0) = (k X0 (σ X2)) ∨ (M.op (σ X2) (σ X2)) = (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1)))) ∨ (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1)))) = (M.op (σ X2) (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52830 X0 X1 X2
       have i₂ := eq18 X0 X2
       grind)
    | exact superpose eq18 eq52830
    | (have j0 := eq52830 X0 X1 X2
       grind)
    | exact resolve eq52830 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52830
  have eq52895 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X2)) = (k X0 (σ (σ (M.op (M.op (τ (τ (k X0 X0))) X1) X1)))) ∨ (M.op (σ X2) X0) = (k X0 (σ X2)) ∨ (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1)))) = (M.op (σ X2) (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52875 X0 X1 X2
       have i₂ := eq48167 X0
       grind)
    | exact superpose eq48167 eq52875
    | (have j0 := eq52875 X0 X1 X2
       grind)
    | exact resolve eq52875 eq48167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52875
  have eq52902 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X2)) = (k X0 (σ (σ (M.op (M.op (τ (τ (M.op X0 X0))) X1) X1)))) ∨ (M.op (σ X2) X0) = (k X0 (σ X2)) ∨ (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1)))) = (M.op (σ X2) (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52895 X0 X1 X2
       have i₂ := eq48186 X0
       grind)
    | exact superpose eq48186 eq52895
    | (have j0 := eq52895 X0 X1 X2
       grind)
    | exact resolve eq52895 eq48186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52895
  have eq52906 : ∀ X0 X1 X2 : G, (M.op (σ X2) (σ X2)) = X0 ∨ (M.op (σ X2) X0) = (k X0 (σ X2)) ∨ (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1)))) = (M.op (σ X2) (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52902 X0 X1 X2
       have i₂ := eq49525 X0 X1
       grind)
    | exact superpose eq49525 eq52902
    | (have j0 := eq52902 X0 X1 X2
       grind)
    | exact resolve eq52902 eq49525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52902
  have eq52908 : ∀ X0 X1 X2 : G, (σ (M.op X2 X2)) = X0 ∨ (M.op (σ X2) X0) = (k X0 (σ X2)) ∨ (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1)))) = (M.op (σ X2) (k X0 (σ (σ (M.op (M.op (τ (M.op (τ X0) (τ X0))) X1) X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52906 X0 X1 X2
       have i₂ := eq48423 X2
       grind)
    | exact superpose eq48423 eq52906
    | (have j0 := eq52906 X0 X1 X2
       grind)
    | exact resolve eq52906 eq48423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48423 eq52906
  have eq52910 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (M.op (M.op (τ (τ (k X0 X0))) X1) X1)))) = (M.op (σ X2) (k X0 (σ (σ (M.op (M.op (τ (τ (k X0 X0))) X1) X1))))) ∨ (σ (M.op X2 X2)) = X0 ∨ (M.op (σ X2) X0) = (k X0 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52908 X0 X1 X2
       have i₂ := eq48167 X0
       grind)
    | exact superpose eq48167 eq52908
    | (have j0 := eq52908 X0 X1 X2
       grind)
    | exact resolve eq52908 eq48167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52908
  have eq52912 : ∀ X0 X1 X2 : G, (k X0 (σ (σ (M.op (M.op (τ (τ (M.op X0 X0))) X1) X1)))) = (M.op (σ X2) (k X0 (σ (σ (M.op (M.op (τ (τ (M.op X0 X0))) X1) X1))))) ∨ (σ (M.op X2 X2)) = X0 ∨ (M.op (σ X2) X0) = (k X0 (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52910 X0 X1 X2
       have i₂ := eq48186 X0
       grind)
    | exact superpose eq48186 eq52910
    | (have j0 := eq52910 X0 X1 X2
       grind)
    | exact resolve eq52910 eq48186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52910
  have eq52914 : ∀ X0 X2 : G, (M.op (σ X2) X0) = X0 ∨ (σ (M.op X2 X2)) = X0 ∨ (M.op (σ X2) X0) = (k X0 (σ X2)) := by
    intro X0 X2
    first
    | (have i₁ := eq52912 X0 x X2
       have i₂ := eq49525 X0 x
       grind)
    | exact superpose eq49525 eq52912
    | (have j0 := eq52912 X0 x X2
       grind)
    | exact resolve eq52912 eq49525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49525 eq52912
  have eq52915 : ∀ X0 X2 : G, (M.op (σ X2) X0) = (k X0 (σ X2)) ∨ (σ (M.op X2 X2)) = X0 := by
    intro X0 X2
    first
    | (have j0 := eq52914 X0 X2
       have j1 := eq12 X0 (σ X2)
       grind)
    | (have r₁ := eq52914 X0 X2
       have r₂ := eq12 X0 (σ X2)
       grind)
    | (have r₁ := eq52914 (M.op x (σ (M.op X2 X2))) X2
       have r₂ := eq12 (σ (M.op X2 X2)) x
       grind)
    | exact resolve eq52914 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52914
  have eq65345 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (σ (M.op (τ X0) (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq52915 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq52915
    | (have j0 := eq52915 X1 (τ X0)
       grind)
    | exact resolve eq52915 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65506 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq52915 (σ X1) X0
       grind)
    | exact superpose eq52915 eq15
    | (have j1 := eq52915 (σ X1) X0
       grind)
    | exact resolve eq15 eq52915
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52915
  have eq65725 : ∀ X0 X1 : G, (σ (τ (k X0 X0))) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq65345 X0 X1
       have i₂ := eq48167 X0
       grind)
    | exact superpose eq48167 eq65345
    | (have j0 := eq65345 X0 X1
       grind)
    | exact resolve eq65345 eq48167
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48167 eq65345
  have eq65822 : ∀ X0 X1 : G, (k X0 X0) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq65725 X0 X1
       have i₂ := eq11 (k X0 X0)
       grind)
    | exact superpose eq11 eq65725
    | (have j0 := eq65725 X0 X1
       grind)
    | exact resolve eq65725 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65725
  have eq65866 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq65822 X0 X1
       have i₂ := eq48186 X0
       grind)
    | exact superpose eq48186 eq65822
    | (have j0 := eq65822 X0 X1
       grind)
    | exact resolve eq65822 eq48186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48186 eq65822
  have eq66249 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq65866 X0 (τ X1)
       grind)
    | exact superpose eq65866 eq18
    | (have j1 := eq65866 X0 (τ X1)
       grind)
    | exact resolve eq18 eq65866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq65866
  have eq71438 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq66249 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq66249
    | exact resolve eq66249 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66249
  have eq71668 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq71438 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq71438
    | (have j0 := eq71438 X0 X1
       grind)
    | exact resolve eq71438 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71438
  have eq85889 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65506 x y
       grind)
    | exact superpose eq65506 eq16
    | (have j1 := eq65506 x y
       grind)
    | exact resolve eq16 eq65506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65506
  have eq86483 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq85889
       have i₂ := eq71668 y x
       grind)
    | exact superpose eq71668 eq85889
    | (have j1 := eq71668 y x
       grind)
    | (have r₁ := eq85889
       have r₂ := eq71668 y x
       grind)
    | exact resolve eq85889 eq71668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71668 eq85889
  have eq86486 : (σ y) = (σ (M.op x x)) ∨ y = (M.op x x) := by grind
  clear eq86483
  have eq86915 : (M.op x x) = (τ (σ y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq86486
       grind)
    | exact superpose eq86486 eq10
    | exact resolve eq10 eq86486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86486
  have eq87047 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq86915
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq86915
    | exact resolve eq86915 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86915
  have eq87048 : y = (M.op x x) := by grind
  clear eq87047
  have eq87127 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq49695 x
       have i₂ := eq87048
       grind)
    | exact superpose eq87048 eq49695
    | exact resolve eq49695 eq87048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49695
  have eq87147 : y = (M.op x y) := by
    first
    | (have i₁ := eq22 x x
       have i₂ := eq87048
       grind)
    | exact superpose eq87048 eq22
    | exact resolve eq22 eq87048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq87048
  have eq89300 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq87127
       grind)
    | exact superpose eq87127 eq16
    | exact resolve eq16 eq87127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87127
  have eq89554 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq89300
       have i₂ := eq87147
       grind)
    | exact superpose eq87147 eq89300
    | exact resolve eq89300 eq87147
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87147 eq89300
  have eq89555 : False := by grind
  exact eq89555
