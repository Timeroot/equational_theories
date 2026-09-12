import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation723`: `x = y ◇ (y ◇ ((z ◇ x) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_y_pyx_Equation723 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law723 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law723.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq92 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op (M.op X0 X1) X1)) = (M.op X3 (M.op X3 (M.op X1 (M.op X2 (M.op (M.op X0 X1) X1))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 (M.op X2 (M.op (M.op X0 X1) X1)) X3 X2
       have i₂ := eq9 X1 X2 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X2 (M.op (M.op X0 X1) X1)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X1) X1) (M.op X2 (M.op (M.op X0 X1) X1)) X2
       have i₂ := eq9 X1 (M.op X2 (M.op (M.op X0 X1) X1)) X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq440 : ∀ X0 X1 X2 : G, (M.op X1 (M.op (M.op X0 X1) X1)) = (M.op X2 (M.op X2 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq92 X0 X1 X1 X2
       have i₂ := eq9 X1 X1 X0
       grind)
    | exact superpose eq9 eq92
    | exact resolve eq92 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq469 : ∀ X0 X2 X3 : G, (M.op X0 (M.op X0 X2)) = (M.op X3 (M.op X3 X2)) := by
    intro X0 X2 X3
    first
    | (have i₁ := eq440 x X2 X3
       have i₂ := eq440 x X2 X0
       grind)
    | exact superpose eq440 eq440
    | exact resolve eq440 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq480 : ∀ X0 X2 : G, (M.op X2 (M.op X0 (M.op X0 X2))) = X2 := by
    intro X0 X2
    first
    | (have i₁ := eq9 X2 X2 x
       have i₂ := eq440 x X2 X0
       grind)
    | exact superpose eq440 eq9
    | exact resolve eq9 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq538 : ∀ X0 : G, (M.op X0 X0) = (M.op (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq480 X0 (M.op X0 X0)
       have i₂ := eq480 X0 X0
       grind)
    | exact superpose eq480 eq480
    | exact resolve eq480 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq544 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X1 X0))) = (M.op (M.op X2 (M.op X0 (M.op X1 (M.op X1 X0)))) (M.op X1 (M.op X1 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq93 X2 (M.op X0 (M.op X0 X2)) X2
       have i₂ := eq480 X0 X2
       grind)
    | exact superpose eq480 eq93
    | exact resolve eq93 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq549 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X0) (M.op X1 (M.op X1 X0))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq544 X2 X0 X2
       have i₂ := eq480 X0 X2
       grind)
    | (have i₁ := eq544 X0 X1 X2
       have i₂ := eq480 X0 (M.op X0 (M.op X1 (M.op X1 X0)))
       grind)
    | exact superpose eq480 eq544
    | exact resolve eq544 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq560 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (M.op X0 X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 X0
       have i₂ := eq538 X0
       grind)
    | exact superpose eq538 eq9
    | exact resolve eq9 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq567 : ∀ X0 : G, (M.op X0 (M.op (M.op X0 X0) (M.op X0 X0))) = X0 := by
    intro X0
    first
    | (have i₁ := eq480 (M.op X0 X0) X0
       have i₂ := eq538 X0
       grind)
    | exact superpose eq538 eq480
    | exact resolve eq480 eq538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480 eq538
  have eq638 : ∀ X0 X1 X2 : G, (M.op X1 X0) = (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq469 X2 (M.op X1 (M.op X0 X0)) X1
       have i₂ := eq560 X0 X1
       grind)
    | exact superpose eq560 eq469
    | exact resolve eq469 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq931 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X2 (M.op X2 (M.op X1 (M.op X0 X0))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq549 (M.op X1 (M.op X0 X0)) X2 X1
       have i₂ := eq560 X0 X1
       grind)
    | exact superpose eq560 eq549
    | exact resolve eq549 eq560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq984 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = (M.op X0 (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq931 X0 X1 x
       have i₂ := eq638 X0 X1 x
       grind)
    | exact superpose eq638 eq931
    | exact resolve eq931 eq638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq638 eq931
  have eq1301 : ∀ X0 X1 : G, (M.op X0 (M.op (M.op X0 X1) (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq984 (M.op X0 X1) X0
       have i₂ := eq549 X1 X0 X0
       grind)
    | exact superpose eq549 eq984
    | exact resolve eq984 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549 eq984
  have eq1622 : ∀ X0 X1 : G, (M.op X1 (M.op (M.op X1 X1) (M.op X1 X1))) = X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1301 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq1301 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq1301
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq1301 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1301
  have eq1648 : ∀ X0 X1 : G, X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1622 X0 X1
       have i₂ := eq567 X1
       grind)
    | exact superpose eq567 eq1622
    | (have j0 := eq1622 X0 X1
       grind)
    | exact resolve eq1622 eq567
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq567 eq1622
  have eq1649 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1648 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648
  have eq1670 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1649 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1649
    | (have j0 := eq1649 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq1649 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1681 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq1649 X0 (τ X1)
       grind)
    | exact superpose eq1649 eq19
    | (have j1 := eq1649 (k (σ X0) X1) (σ (M.op (τ X1) X0))
       grind)
    | exact resolve eq19 eq1649
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq1649
  have eq18830 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1681 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1681
    | exact resolve eq1681 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1681
  have eq18984 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18830 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq18830
    | (have j0 := eq18830 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq18830 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18830
  have eq52761 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1670 y x
       grind)
    | exact superpose eq1670 eq16
    | (have j1 := eq1670 x y
       grind)
    | exact resolve eq16 eq1670
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670
  have eq52894 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52761
       have i₂ := eq18984 x y
       grind)
    | exact superpose eq18984 eq52761
    | (have j1 := eq18984 (σ x) (σ y)
       grind)
    | (have r₁ := eq52761
       have r₂ := eq18984 x y
       grind)
    | (have r₁ := eq52761
       have r₂ := eq18984 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq52761
       have r₂ := eq18984 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq52761 eq18984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18984 eq52761
  have eq52895 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq52894
  have eq52902 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq52895
       grind)
    | exact superpose eq52895 eq10
    | exact resolve eq10 eq52895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52895
  have eq52987 : x = y ∨ x = y := by
    first
    | (have i₁ := eq52902
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq52902
    | exact resolve eq52902 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52902
  have eq52988 : x = y := by grind
  clear eq52987
  have eq52995 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq52988
       grind)
    | exact superpose eq52988 eq16
    | exact resolve eq16 eq52988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52988
  have eq52996 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq52995
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq52995
    | (have r₁ := eq52995
       have r₂ := eq22 x
       grind)
    | exact resolve eq52995 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq52995
  have eq52997 : False := by grind
  exact eq52997

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pxy_pyx_pyx_pxy_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X1 := by
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
  have eq87 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq588 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq87 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq87 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq87 X0 X1
       grind)
    | exact resolve eq12 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq87 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq87 X0 X1
       grind)
    | exact superpose eq87 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq87 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq87 X0 X1
       grind)
    | exact resolve eq13 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq610 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq589 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589
  have eq615 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq610 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq610 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq610 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq610 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq610
  have eq616 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq588 X0 X1
       have j1 := eq12 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq588 X0 X1
       have r₂ := eq12 (σ X1) (σ X0)
       grind)
    | exact resolve eq588 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq623 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq615 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq615
    | (have j0 := eq615 X0 X1
       grind)
    | exact resolve eq615 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq615
  have eq624 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq623 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq623
  have eq625 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq616 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq616
    | (have j0 := eq616 X0 X1
       grind)
    | exact resolve eq616 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq626 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq625 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq625
  have eq629 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq626 X0 X1
       have j1 := eq624 X0 X1
       grind)
    | (have r₁ := eq626 X0 X1
       have r₂ := eq624 X0 X1
       grind)
    | exact resolve eq626 eq624
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq624 eq626
  have eq630 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq629 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq629
    | exact resolve eq629 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq642 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq629 x y
       grind)
    | exact superpose eq629 eq16
    | exact resolve eq16 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq741 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq630 X0 (τ X1)
       grind)
    | exact superpose eq630 eq17
    | exact resolve eq17 eq630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq630
  have eq759 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq741 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq741
    | exact resolve eq741 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq741
  have eq767 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq759 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq759
    | exact resolve eq759 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq786 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq642
       have i₂ := eq767 x y
       grind)
    | exact superpose eq767 eq642
    | exact resolve eq642 eq767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq642 eq767
  have eq787 : False := by grind
  exact eq787

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(Y,Y) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_pyx_pxx_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
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
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
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
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq14 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
       have i₂ := eq14 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (σ (k y (τ X0))) = (k (σ y) X0) := by
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
  have eq71 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq72 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq65 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq65
    | (have j0 := eq65 X0 (σ X1)
       grind)
    | exact resolve eq65 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq71
       have i₂ := eq65 y x
       grind)
    | exact superpose eq65 eq71
    | (have j1 := eq65 x x
       grind)
    | exact resolve eq71 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq92
    | exact resolve eq92 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq99 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq16
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq113 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
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
  clear eq37
  have eq174 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq65 (σ X0) sF3
       grind)
    | exact superpose eq65 eq40
    | (have j1 := eq65 X0 (σ y)
       grind)
    | exact resolve eq40 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq257 : ∀ X0 X1 X2 : G, (σ (k (k (τ X0) X1) X2)) = (k (k X0 (σ X1)) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k (τ X0) X1) X2
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq10
    | exact resolve eq10 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq279 : ∀ X0 : G, (k (σ (M.op x y)) X0) = (σ (M.op (τ X0) (M.op x y))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq113 X0
       have i₂ := eq65 sF0 (τ X0)
       grind)
    | exact superpose eq65 eq113
    | (have j1 := eq65 X0 (τ X0)
       grind)
    | exact resolve eq113 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq304 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq38 X0 X1
       have i₂ := eq65 X1 (τ X0)
       grind)
    | exact superpose eq65 eq38
    | (have j1 := eq65 X0 (τ X0)
       grind)
    | exact resolve eq38 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq473 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq50 X1 X4 x x
       have i₂ := eq50 X1 X0 x x
       grind)
    | (have i₁ := eq50 X0 X1 x x
       have i₂ := eq50 X0 (M.op x x) x x
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq478 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X1 X1) (M.op (M.op X2 X2) (M.op X3 (M.op (M.op X4 X4) X0)))) = (M.op X3 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq50 (M.op X3 (M.op (M.op X4 X4) X0)) X3 X1 X2
       have i₂ := eq14 X0 X3 X4
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X3) (M.op (M.op X4 X4) (M.op X5 X2))) = (M.op X5 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq50 (M.op X5 X2) X5 X3 X4
       have i₂ := eq50 X2 X5 X0 X1
       grind)
    | (have i₁ := eq50 (M.op (M.op X3 X3) X0) (M.op X2 X2) X2 X3
       have i₂ := eq50 X0 X1 X2 X3
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq490 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X4) X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14 (M.op (M.op X4 X4) X1) X2 x
       have i₂ := eq50 X1 X0 x X4
       grind)
    | (have i₁ := eq14 (M.op (M.op X2 X2) X0) X1 X2
       have i₂ := eq50 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq491 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X2 X2) x
       have i₂ := eq50 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq50 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq493 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op X0 (M.op X0 (M.op X1 X1))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 X3 (M.op (M.op X1 X1) (M.op X1 X1)) X2
       have i₂ := eq50 (M.op X1 X1) X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq50 eq51
    | exact resolve eq51 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq79 X0 X0
       grind)
    | exact superpose eq79 eq12
    | (have j0 := eq12 X1 (σ X0)
       have j1 := eq79 X0 X0
       grind)
    | (have r₁ := eq12 X0 (σ X1)
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq634 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) (σ X0))) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 (σ X0) (σ X1) X2 X3
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq50
    | (have j1 := eq79 X0 X1
       grind)
    | exact resolve eq50 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq636 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq79 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq637 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op (σ X0) X1) = X1 ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq632 X0 X1
       have j1 := eq12 X1 (σ X0)
       grind)
    | (have r₁ := eq632 X0 (σ X0)
       have r₂ := eq12 X0 (σ X0)
       grind)
    | (have r₁ := eq632 X0 X1
       have r₂ := eq12 X0 (σ X0)
       grind)
    | exact resolve eq632 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq654 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq93 eq65
    | (have j0 := eq65 x (σ x)
       grind)
    | exact resolve eq65 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq655 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq654
    | exact resolve eq654 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq654
  have eq658 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq655
       have r₂ := eq27
       grind)
    | exact resolve eq655 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq655
  have eq666 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq658 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq658
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq658
       grind)
    | exact resolve eq13 eq658
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658
  have eq667 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq666
  have eq670 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq667 eq49
    | exact resolve eq49 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq667
  have eq674 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq670
    | exact resolve eq670 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq670
  have eq677 : x = (M.op x x) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq65 x x
       have i₂ := eq674
       grind)
    | exact superpose eq674 eq65
    | (have j0 := eq65 x x
       grind)
    | exact resolve eq65 eq674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674
  have eq678 : x = (M.op x x) := by grind
  clear eq677
  have eq683 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X1) = (M.op x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X1 x X0
       have i₂ := eq678
       grind)
    | exact superpose eq678 eq51
    | exact resolve eq51 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq686 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op x X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 x
       have i₂ := eq678
       grind)
    | exact superpose eq678 eq14
    | exact resolve eq14 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq687 : x ≠ x ∨ x = (k x x) := by
    first
    | (have i₁ := eq13 x x
       have i₂ := eq678
       grind)
    | exact superpose eq678 eq13
    | (have r₁ := eq13 x x
       have r₂ := eq678
       grind)
    | exact resolve eq13 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq688 : x = (k x x) := by grind
  clear eq687
  have eq707 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq688
       grind)
    | exact superpose eq688 eq43
    | exact resolve eq43 eq688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq688
  have eq711 : (σ x) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq707
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq707
    | exact resolve eq707 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq714 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq711 eq65
    | (have j0 := eq65 x (σ x)
       grind)
    | exact resolve eq65 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq715 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq714
  have eq831 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq491 X0 X1 x
       have i₂ := eq678
       grind)
    | exact superpose eq678 eq491
    | exact resolve eq491 eq678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq978 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 X1) (M.op (σ y) (σ (k X0 y)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0 X1
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1⟩ := hcon
    have f978_13 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
      intro X0 X1 X2
      grind
    have f978_14 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
      intro X0
      grind
    have f978_23 : (σ X0) ≠ (M.op (M.op X1 X1) (M.op (σ y) (σ (k X0 y)))) := by grind
    have f978_24 : (σ y) ≠ (M.op (σ y) (σ y)) := by grind
    have f978_26 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ y) (σ X0)) := by
      intro X0
      first
      | (have j0 := f978_14 X0
         grind)
      | (have r₁ := f978_14 X0
         have r₂ := f978_24
         grind)
      | exact resolve f978_14 f978_24
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f978_33 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 X1) (M.op (σ y) (σ (k X0 y)))) := by
      intro X0 X1
      first
      | (have i₁ := f978_13 (σ y) (σ X0) X1
         have i₂ := f978_26 X0
         grind)
      | exact superpose f978_26 f978_13
      | exact resolve f978_13 f978_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f978_36 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 X1) (σ (k (k X0 y) y))) := by
      intro X0 X1
      first
      | (have i₁ := f978_33 X0 X1
         have i₂ := f978_26 (k X0 y)
         grind)
      | exact superpose f978_26 f978_33
      | exact resolve f978_33 f978_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f978_91 : (σ X0) ≠ (M.op (M.op X1 X1) (σ (k (k X0 y) y))) := by
      first
      | (have i₁ := f978_23
         have i₂ := f978_26 (k X0 y)
         grind)
      | exact superpose f978_26 f978_23
      | exact resolve f978_23 f978_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f978_92 : False := by
      first
      | (have r₁ := f978_91
         have r₂ := f978_36 X0 X1
         grind)
      | exact resolve f978_91 f978_36
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    exact f978_92
  have eq1091 : ∀ X0 : G, (M.op (σ x) X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq715 eq683
    | exact resolve eq683 eq715
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq1178 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq26 eq1091
    | (have j0 := eq1091 (σ y)
       grind)
    | exact resolve eq1091 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1204 : ∀ X0 : G, (M.op x X0) ≠ X0 ∨ (k X0 (σ x)) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq1091 eq13
    | (have j0 := eq13 X0 x
       grind)
    | exact resolve eq13 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1261 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op x (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq1178 eq491
    | exact resolve eq491 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1265 : (σ y) = (M.op x (M.op x (M.op (σ x) (σ y)))) := by
    first
    | (have i₁ := eq1261 x
       have i₂ := eq683 x (M.op x sF4)
       grind)
    | exact superpose eq683 eq1261
    | exact resolve eq1261 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq1311 : ∀ X0 : G, (σ y) = (M.op X0 (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq1265
       have i₂ := eq473 x sF4 x
       grind)
    | (have i₁ := eq1265
       have i₂ := eq473 X0 sF4 x
       grind)
    | exact superpose eq473 eq1265
    | exact resolve eq1265 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1265
  have eq1342 : ∀ X0 X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op (M.op X0 X0) (M.op X1 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq1311 eq491
    | exact resolve eq491 eq1311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311
  have eq1363 : ∀ X1 : G, (M.op X1 (M.op (σ x) (σ y))) = (M.op x (M.op X1 (σ y))) := by
    intro X1
    first
    | (have i₁ := eq1342 x X1
       have i₂ := eq683 x (M.op X1 sF3)
       grind)
    | exact superpose eq683 eq1342
    | exact resolve eq1342 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342
  have eq1479 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq686 X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq686
    | (have j0 := eq686 X0 y
       grind)
    | exact resolve eq686 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1625 : ∀ X0 X1 : G, (M.op X1 (M.op x y)) = (M.op (M.op X0 X0) (M.op X1 y)) := by
    intro X0 X1
    first
    | exact superpose eq1479 eq491
    | exact resolve eq491 eq1479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq491
  have eq1647 : ∀ X1 : G, (M.op X1 (M.op x y)) = (M.op x (M.op X1 y)) := by
    intro X1
    first
    | (have i₁ := eq1625 x X1
       have i₂ := eq683 x (M.op X1 y)
       grind)
    | exact superpose eq683 eq1625
    | exact resolve eq1625 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625
  have eq3999 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) = (M.op x X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq490 X0 X1 X2 x
       have i₂ := eq683 x X1
       grind)
    | exact superpose eq683 eq490
    | exact resolve eq490 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq4089 : ∀ X0 X1 : G, (M.op X1 (M.op x X0)) = (M.op x (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3999 X1 (M.op X1 X0) X1
       have i₂ := eq3999 X1 X0 X1
       grind)
    | exact superpose eq3999 eq3999
    | exact resolve eq3999 eq3999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4090 : ∀ X0 X1 X2 : G, (M.op x X2) = (M.op X1 (M.op X0 (M.op X0 (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3999 X1 X2 X1
       have i₂ := eq473 X1 (M.op X1 X2) X0
       grind)
    | (have i₁ := eq3999 X1 X2 X1
       have i₂ := eq473 X0 (M.op X1 X2) X1
       grind)
    | exact superpose eq473 eq3999
    | exact resolve eq3999 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3999
  have eq4331 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op x X1))) = (M.op X0 (M.op x (M.op X0 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq473 X2 (M.op x X1) X0
       have i₂ := eq4089 X1 X0
       grind)
    | (have i₁ := eq473 X0 (M.op X1 X0) x
       have i₂ := eq4089 X0 X1
       grind)
    | exact superpose eq4089 eq473
    | exact resolve eq473 eq4089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473
  have eq4383 : ∀ X0 X1 : G, (M.op X0 (M.op x (M.op X0 X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4331 X0 X1 x
       have i₂ := eq686 x X1
       grind)
    | exact superpose eq686 eq4331
    | exact resolve eq4331 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4331
  have eq4627 : ∀ X0 X1 X3 : G, (M.op (M.op X0 (M.op X0 (M.op X1 X1))) X3) = (M.op x X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq493 X0 X1 x X3
       have i₂ := eq683 x X3
       grind)
    | exact superpose eq683 eq493
    | exact resolve eq493 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq4664 : ∀ X0 X1 : G, (M.op x X1) = (M.op (M.op x (M.op X0 (M.op x X0))) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4627 x X0 X1
       have i₂ := eq4089 X0 X0
       grind)
    | (have i₁ := eq4627 X1 x x
       have i₂ := eq4089 x X1
       grind)
    | exact superpose eq4089 eq4627
    | exact resolve eq4627 eq4089
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4089 eq4627
  have eq5537 : (σ (σ x)) ≠ (σ (σ x)) ∨ (σ (σ x)) = (M.op (σ (σ x)) (σ (σ x))) := by
    first
    | exact superpose eq711 eq636
    | (have j0 := eq636 (σ x)
       grind)
    | exact resolve eq636 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5540 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq636 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq636
    | (have j0 := eq636 (τ X0)
       grind)
    | exact resolve eq636 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq636
  have eq5545 : (σ (σ x)) = (M.op (σ (σ x)) (σ (σ x))) := by grind
  clear eq5537
  have eq5551 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq5540 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5540
    | (have j0 := eq5540 X0
       grind)
    | exact resolve eq5540 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5540
  have eq5557 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5551 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq5551
    | (have j0 := eq5551 X0
       grind)
    | exact resolve eq5551 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5551
  have eq5569 : ∀ X0 : G, (M.op x X0) = (M.op (σ (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq5545 eq683
    | exact resolve eq683 eq5545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5545
  have eq6606 : ∀ X0 X1 X2 X3 : G, (k (σ (M.op (τ X3) X2)) X3) = (σ (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))) ∨ (τ X3) = (M.op (τ X3) (τ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq304 X3 (M.op (τ X3) X2)
       have i₂ := eq50 X2 (τ X3) X0 X1
       grind)
    | exact superpose eq50 eq304
    | (have j0 := eq304 X3 X1
       grind)
    | exact resolve eq304 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq304
  have eq6659 : ∀ X1 X2 X3 : G, (k (σ (M.op (τ X3) X2)) X3) = (σ (M.op x (M.op (M.op X1 X1) X2))) ∨ (τ X3) = (M.op (τ X3) (τ X3)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq6606 x X1 X2 X3
       have i₂ := eq683 x (M.op (M.op X1 X1) X2)
       grind)
    | exact superpose eq683 eq6606
    | (have j0 := eq6606 x X1 X2 X3
       grind)
    | exact resolve eq6606 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6606
  have eq6667 : ∀ X2 X3 : G, (k (σ (M.op (τ X3) X2)) X3) = (σ (M.op x (M.op x X2))) ∨ (τ X3) = (M.op (τ X3) (τ X3)) := by
    intro X2 X3
    first
    | (have i₁ := eq6659 x X2 X3
       have i₂ := eq683 x X2
       grind)
    | exact superpose eq683 eq6659
    | (have j0 := eq6659 x X2 X3
       grind)
    | exact resolve eq6659 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6659
  have eq7792 : ∀ X0 X2 X3 X4 : G, (M.op X3 X0) = (M.op x (M.op (M.op X2 X2) (M.op X3 (M.op (M.op X4 X4) X0)))) := by
    intro X0 X2 X3 X4
    first
    | (have i₁ := eq478 X0 x X2 X3 X4
       have i₂ := eq683 x (M.op (M.op X2 X2) (M.op X3 (M.op (M.op X4 X4) X0)))
       grind)
    | exact superpose eq683 eq478
    | exact resolve eq478 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq7793 : ∀ X0 X3 X4 : G, (M.op X3 X0) = (M.op x (M.op x (M.op X3 (M.op (M.op X4 X4) X0)))) := by
    intro X0 X3 X4
    first
    | (have i₁ := eq7792 X0 x X3 X4
       have i₂ := eq683 x (M.op X3 (M.op (M.op X4 X4) X0))
       grind)
    | exact superpose eq683 eq7792
    | exact resolve eq7792 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7792
  have eq7794 : ∀ X0 X3 : G, (M.op X3 X0) = (M.op x (M.op x (M.op X3 (M.op x X0)))) := by
    intro X0 X3
    first
    | (have i₁ := eq7793 X0 X3 x
       have i₂ := eq683 x X0
       grind)
    | exact superpose eq683 eq7793
    | exact resolve eq7793 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7793
  have eq10098 : ∀ X0 : G, (σ (σ x)) ≠ (σ (σ x)) ∨ (M.op (σ (σ x)) X0) = X0 ∨ (M.op X0 X0) = (k X0 (σ (σ x))) := by
    intro X0
    first
    | exact superpose eq711 eq637
    | (have j0 := eq637 (σ x) X0
       grind)
    | exact resolve eq637 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10102 : ∀ X0 : G, (σ x) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) X0) = X0 ∨ (M.op X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq637 x X0
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq637
    | (have j0 := eq637 x X0
       grind)
    | exact resolve eq637 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq637
  have eq10106 : ∀ X0 : G, (M.op (σ (σ x)) X0) = X0 ∨ (M.op X0 X0) = (k X0 (σ (σ x))) := by
    intro X0
    first
    | (have j0 := eq10098 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10098
  have eq10112 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (M.op (σ x) X0) = X0 ∨ (M.op X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq711 eq10102
    | (have j0 := eq10102 X0
       grind)
    | (have r₁ := eq10102 X0
       have r₂ := eq711
       grind)
    | exact resolve eq10102 eq711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq10102
  have eq10115 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ (σ x))) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | exact superpose eq5569 eq10106
    | (have j0 := eq10106 X0
       grind)
    | exact resolve eq10106 eq5569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5569 eq10106
  have eq10120 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (M.op X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have j0 := eq10112 X0
       grind)
    | (have r₁ := eq10112 X0
       have r₂ := eq22
       grind)
    | exact resolve eq10112 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10112
  have eq10127 : ∀ X0 : G, (M.op (σ x) X0) = X0 ∨ (M.op X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10120 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10120
    | (have j0 := eq10120 X0
       grind)
    | exact resolve eq10120 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10120
  have eq10132 : ∀ X0 : G, (M.op x X0) = X0 ∨ (M.op X0 X0) = (k X0 (σ x)) := by
    intro X0
    first
    | exact superpose eq1091 eq10127
    | (have j0 := eq10127 X0
       grind)
    | exact resolve eq10127 eq1091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1091 eq10127
  have eq10134 : ∀ X0 : G, (M.op X0 X0) = (k X0 (σ x)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10132 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq10132
    | (have j0 := eq10132 X0
       grind)
    | exact resolve eq10132 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq10132
  have eq10136 : ∀ X1 X2 X3 X4 X5 : G, (M.op (M.op X3 X3) (M.op (M.op X4 X4) (M.op X5 X2))) = (M.op X5 (M.op x (M.op (M.op X1 X1) X2))) := by
    intro X1 X2 X3 X4 X5
    first
    | (have i₁ := eq479 x X1 X2 X3 X4 X5
       have i₂ := eq683 x (M.op (M.op X1 X1) X2)
       grind)
    | exact superpose eq683 eq479
    | exact resolve eq479 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479
  have eq10137 : ∀ X2 X3 X4 X5 : G, (M.op (M.op X3 X3) (M.op (M.op X4 X4) (M.op X5 X2))) = (M.op X5 (M.op x (M.op x X2))) := by
    intro X2 X3 X4 X5
    first
    | (have i₁ := eq10136 x X2 X3 X4 X5
       have i₂ := eq683 x X2
       grind)
    | exact superpose eq683 eq10136
    | exact resolve eq10136 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10136
  have eq10138 : ∀ X2 X4 X5 : G, (M.op X5 (M.op x (M.op x X2))) = (M.op x (M.op (M.op X4 X4) (M.op X5 X2))) := by
    intro X2 X4 X5
    first
    | (have i₁ := eq10137 X2 x X4 X5
       have i₂ := eq683 x (M.op (M.op X4 X4) (M.op X5 X2))
       grind)
    | exact superpose eq683 eq10137
    | exact resolve eq10137 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10137
  have eq10139 : ∀ X2 X5 : G, (M.op X5 (M.op x (M.op x X2))) = (M.op x (M.op x (M.op X5 X2))) := by
    intro X2 X5
    first
    | (have i₁ := eq10138 X2 x X5
       have i₂ := eq683 x (M.op X5 X2)
       grind)
    | exact superpose eq683 eq10138
    | exact resolve eq10138 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10138
  have eq10141 : ∀ X0 X1 X2 : G, (M.op X2 (M.op x (M.op X0 X1))) = (M.op x (M.op x (M.op X2 (M.op x (M.op X0 (M.op x X1)))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10139 (M.op x (M.op X0 (M.op x X1))) X2
       have i₂ := eq7794 X1 X0
       grind)
    | exact superpose eq7794 eq10139
    | exact resolve eq10139 eq7794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10139
  have eq10475 : ∀ X0 X1 X2 : G, (M.op X2 (M.op x (M.op X0 X1))) = (M.op X2 (M.op X0 (M.op x X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10141 X0 X1 X2
       have i₂ := eq7794 (M.op X0 (M.op x X1)) X2
       grind)
    | exact superpose eq7794 eq10141
    | exact resolve eq10141 eq7794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10141
  have eq12824 : ∀ X0 X1 X3 : G, (M.op (σ X1) (σ (k X0 X1))) = (M.op x (M.op (M.op X3 X3) (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq634 X0 X1 x X3
       have i₂ := eq683 x (M.op (M.op X3 X3) (σ X0))
       grind)
    | exact superpose eq683 eq634
    | (have j0 := eq634 X0 X1 x X3
       grind)
    | exact resolve eq634 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq634
  have eq12825 : ∀ X0 X1 : G, (M.op (σ X1) (σ (k X0 X1))) = (M.op x (M.op x (σ X0))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12824 X0 X1 x
       have i₂ := eq683 x (σ X0)
       grind)
    | exact superpose eq683 eq12824
    | (have j0 := eq12824 X0 X1 x
       grind)
    | exact resolve eq12824 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12824
  have eq12946 : ∀ X0 : G, (M.op x (M.op x (σ y))) = (M.op (σ (τ X0)) (k (σ y) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq12825 y (τ X0)
       have i₂ := eq67 X0
       grind)
    | exact superpose eq67 eq12825
    | (have j0 := eq12825 X0 (τ X0)
       grind)
    | exact resolve eq12825 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq12825
  have eq13007 : ∀ X0 : G, (M.op x (M.op x (σ y))) = (M.op X0 (k (σ y) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq12946 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq12946
    | (have j0 := eq12946 X0
       grind)
    | exact resolve eq12946 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12946
  have eq13101 : ∀ X0 : G, (M.op x (M.op x (σ y))) = (M.op X0 (k (σ y) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq13007 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq13007
    | (have j0 := eq13007 X0
       grind)
    | exact resolve eq13007 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13007
  have eq13176 : ∀ X0 : G, (M.op x (M.op (σ x) (σ y))) = (M.op X0 (k (σ y) X0)) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | exact superpose eq1363 eq13101
    | (have j0 := eq13101 X0
       grind)
    | exact resolve eq13101 eq1363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1363 eq13101
  have eq13237 : ∀ X0 : G, (M.op x (M.op (σ x) (σ y))) = (M.op X0 (k (σ y) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq13176 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq13176
    | (have j0 := eq13176 X0
       grind)
    | exact resolve eq13176 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13176
  have eq24533 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op x (M.op (σ x) (σ y))))) = (k (σ y) (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | exact superpose eq13237 eq14
    | (have j1 := eq13237 (M.op X1 X1)
       grind)
    | exact resolve eq14 eq13237
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13237
  have eq24613 : ∀ X1 : G, (M.op (σ x) (σ y)) = (k (σ y) (M.op X1 X1)) ∨ (M.op X1 X1) = (M.op (M.op X1 X1) (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq24533 x X1
       have i₂ := eq686 x sF4
       grind)
    | exact superpose eq686 eq24533
    | (have j0 := eq24533 x X1
       grind)
    | exact resolve eq24533 eq686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq686 eq24533
  have eq24657 : ∀ X1 : G, (M.op X1 X1) = (M.op x (M.op X1 X1)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq24613 X1
       have i₂ := eq683 X1 (M.op X1 X1)
       grind)
    | exact superpose eq683 eq24613
    | (have j0 := eq24613 X1
       grind)
    | exact resolve eq24613 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24613
  have eq124156 : ∀ X0 : G, (M.op x (M.op x (M.op X0 (M.op x X0)))) = (k (M.op x (M.op X0 (M.op x X0))) (σ x)) ∨ (M.op x (M.op X0 (M.op x X0))) = (M.op x (M.op x (M.op X0 (M.op x X0)))) := by
    intro X0
    first
    | (have i₁ := eq10134 (M.op x (M.op X0 (M.op x X0)))
       have i₂ := eq4664 X0 (M.op x (M.op X0 (M.op x X0)))
       grind)
    | exact superpose eq4664 eq10134
    | (have j0 := eq10134 (M.op x (M.op X0 (M.op x X0)))
       grind)
    | exact resolve eq10134 eq4664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4664 eq10134
  have eq124791 : ∀ X0 : G, (M.op x (M.op x (M.op X0 (M.op x X0)))) = (k (M.op x (M.op X0 (M.op x X0))) (σ x)) := by
    intro X0
    first
    | (have j0 := eq124156 X0
       have j1 := eq1204 (M.op x (M.op X0 (M.op x X0)))
       grind)
    | (have r₁ := eq124156 X0
       have r₂ := eq1204 (M.op x (M.op X0 (M.op x X0)))
       grind)
    | exact resolve eq124156 eq1204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1204 eq124156
  have eq125157 : ∀ X0 : G, (M.op X0 X0) = (k (M.op x (M.op X0 (M.op x X0))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq124791 X0
       have i₂ := eq7794 X0 X0
       grind)
    | exact superpose eq7794 eq124791
    | exact resolve eq124791 eq7794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7794 eq124791
  have eq143074 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = (k (M.op x (M.op (M.op X0 X0) (M.op x (M.op X1 X1)))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq125157 (M.op X1 X1)
       have i₂ := eq51 (M.op x (M.op X1 X1)) X0 X1
       grind)
    | (have i₁ := eq125157 (M.op X1 X1)
       have i₂ := eq51 (M.op x (M.op X1 X1)) X1 X0
       grind)
    | exact superpose eq51 eq125157
    | exact resolve eq125157 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq125157
  have eq143211 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = (k (M.op x (M.op x (M.op (M.op X0 X0) (M.op X1 X1)))) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq143074 X0 X1
       have i₂ := eq10475 (M.op X0 X0) (M.op X1 X1) x
       grind)
    | exact superpose eq10475 eq143074
    | exact resolve eq143074 eq10475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10475 eq143074
  have eq143347 : ∀ X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = (k (M.op X1 X1) (σ x)) := by
    intro X1
    first
    | (have i₁ := eq143211 x X1
       have i₂ := eq14 (M.op X1 X1) x x
       grind)
    | exact superpose eq14 eq143211
    | exact resolve eq143211 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143211
  have eq143422 : ∀ X1 : G, (M.op x (M.op X1 X1)) = (k (M.op X1 X1) (σ x)) := by
    intro X1
    first
    | (have i₁ := eq143347 X1
       have i₂ := eq683 X1 (M.op X1 X1)
       grind)
    | exact superpose eq683 eq143347
    | exact resolve eq143347 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143347
  have eq325625 : ∀ X0 : G, (k (k (σ (M.op x y)) X0) X0) = (σ (M.op x (M.op x (M.op x y)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | exact superpose eq279 eq6667
    | (have j0 := eq6667 x X0
       have j1 := eq279 X0
       grind)
    | exact resolve eq6667 eq279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279 eq6667
  have eq325791 : ∀ X0 : G, (k (k (σ (M.op x y)) X0) X0) = (σ (M.op x (M.op x (M.op x y)))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq325625 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325625
  have eq325795 : ∀ X0 : G, (σ y) = (k (k (σ (M.op x y)) X0) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | exact superpose eq1479 eq325791
    | (have j0 := eq325791 X0
       grind)
    | exact resolve eq325791 eq1479
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1479 eq325791
  have eq325799 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ y) = (k (k (σ (M.op x y)) X0) X0) := by
    intro X0
    first
    | (have i₁ := eq325795 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq325795
    | (have j0 := eq325795 X0
       grind)
    | exact resolve eq325795 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325795
  have eq332657 : ∀ X0 : G, (σ X0) = (M.op x (M.op (σ y) (σ (k X0 y)))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq978 X0 X0
       have i₂ := eq683 X0 (M.op sF3 (σ (k X0 y)))
       grind)
    | exact superpose eq683 eq978
    | exact resolve eq978 eq683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq683 eq978
  have eq332683 : ∀ X0 : G, (σ X0) = (M.op x (σ (k (k X0 y) y))) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq174 eq332657
    | exact resolve eq332657 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq332657
  have eq332861 : ∀ X0 : G, (σ X0) = (M.op x (σ (k (k X0 y) y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq332683 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332683
  have eq961479 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ y) = (k (k (σ (M.op x y)) (σ X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq325799 (σ X0)
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq325799
    | (have j0 := eq325799 (σ X0)
       grind)
    | exact resolve eq325799 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq325799
  have eq961797 : ∀ X0 : G, (σ y) = (σ (k (k (τ (σ (M.op x y))) X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq961479 x
       have i₂ := eq257 sF1 x x
       grind)
    | exact superpose eq257 eq961479
    | (have j0 := eq961479 X0
       grind)
    | exact resolve eq961479 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq961479
  have eq961813 : ∀ X0 : G, (σ y) = (σ (k (k (M.op x y) X0) X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | exact superpose eq30 eq961797
    | (have j0 := eq961797 X0
       grind)
    | exact resolve eq961797 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq961797
  have eq1037345 : ∀ X0 : G, (M.op x X0) = (M.op X0 (M.op x (M.op X0 X0))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq4090 x X0 X0
       have i₂ := eq24657 X0
       grind)
    | exact superpose eq24657 eq4090
    | (have j1 := eq24657 X0
       grind)
    | exact resolve eq4090 eq24657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4090 eq24657
  have eq1037636 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ y) (M.op X0 X0)) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1037345 X0
       have i₂ := eq4383 X0 X0
       grind)
    | exact superpose eq4383 eq1037345
    | (have j0 := eq1037345 X0
       grind)
    | exact resolve eq1037345 eq4383
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4383 eq1037345
  have eq1038036 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ y) (k X0 (σ (σ x)))) ∨ (M.op x X0) = X0 ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq1037636 X0
       have i₂ := eq10115 X0
       grind)
    | (have i₁ := eq1037636 x
       have i₂ := eq10115 x
       grind)
    | exact superpose eq10115 eq1037636
    | (have j0 := eq1037636 X0
       have j1 := eq10115 X0
       grind)
    | exact resolve eq1037636 eq10115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10115 eq1037636
  have eq1038172 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (σ y) (k X0 (σ (σ x)))) ∨ (M.op x X0) = X0 := by
    intro X0
    first
    | (have j0 := eq1038036 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038036
  have eq1069029 : (M.op (σ x) (σ y)) = (k (σ y) (σ (k y (σ x)))) ∨ (σ y) = (M.op x (σ y)) := by
    first
    | exact superpose eq36 eq1038172
    | (have j0 := eq1038172 (σ y)
       grind)
    | exact resolve eq1038172 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1038172
  have eq1069153 : (M.op (σ x) (σ y)) = (σ (k y (k y (σ x)))) ∨ (σ y) = (M.op x (σ y)) := by
    first
    | exact superpose eq36 eq1069029
    | exact resolve eq1069029 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1069029
  have eq1069197 : (M.op (σ x) (σ y)) = (σ (k y (k y (σ x)))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1178 eq1069153
    | exact resolve eq1069153 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069153
  have eq1069250 : (τ (M.op (σ x) (σ y))) = (k y (k y (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1069197 eq16
    | exact resolve eq16 eq1069197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069197
  have eq1223828 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq961813 eq332861
    | (have j1 := eq961813 (σ y)
       grind)
    | exact resolve eq332861 eq961813
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332861 eq961813
  have eq1224083 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1178 eq1223828
    | exact resolve eq1223828 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1178 eq1223828
  have eq1224149 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq1224083
    | exact resolve eq1224083 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224083
  have eq1224169 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1224149
       have r₂ := eq27
       grind)
    | exact resolve eq1224149 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224149
  have eq1224304 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1224169 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq1224169
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq1224169
       grind)
    | exact resolve eq13 eq1224169
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1224169
  have eq1224388 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1224304
  have eq1225884 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1224388 eq99
    | exact resolve eq99 eq1224388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq1224388
  have eq1226142 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq1225884
    | exact resolve eq1225884 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1225884
  have eq1226145 : y = (M.op y y) := by
    first
    | (have j1 := eq5557 y
       grind)
    | (have r₁ := eq1226142
       have r₂ := eq5557 y
       grind)
    | exact resolve eq1226142 eq5557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5557 eq1226142
  have eq1226252 : (M.op x y) = (k y (σ x)) := by
    first
    | (have i₁ := eq143422 y
       have i₂ := eq1226145
       grind)
    | exact superpose eq1226145 eq143422
    | exact resolve eq143422 eq1226145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143422
  have eq1226271 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1226145
       grind)
    | exact superpose eq1226145 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq1226145
       grind)
    | exact resolve eq13 eq1226145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1226278 : y = (M.op x (M.op y y)) := by
    first
    | (have i₁ := eq831 y y
       have i₂ := eq1226145
       grind)
    | exact superpose eq1226145 eq831
    | exact resolve eq831 eq1226145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226145
  have eq1226355 : y = (k y y) := by grind
  clear eq1226271
  have eq1226432 : y = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1226278
       have i₂ := eq1647 y
       grind)
    | exact superpose eq1647 eq1226278
    | exact resolve eq1226278 eq1647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226278
  have eq1226446 : (M.op x y) = (k y (σ x)) := by
    first
    | (have i₁ := eq1226252
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1226252
    | exact resolve eq1226252 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1226252
  have eq1227909 : (M.op x y) = (M.op x (M.op y y)) := by
    first
    | exact superpose eq1226432 eq831
    | exact resolve eq831 eq1226432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq1228062 : (M.op x y) = (M.op y (M.op x y)) := by
    first
    | (have i₁ := eq1227909
       have i₂ := eq1647 y
       grind)
    | exact superpose eq1647 eq1227909
    | exact resolve eq1227909 eq1647
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1647 eq1227909
  have eq1228164 : y = (M.op x y) := by
    first
    | exact superpose eq1226432 eq1228062
    | exact resolve eq1228062 eq1226432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226432 eq1228062
  have eq1228229 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1228164 eq20
    | exact resolve eq20 eq1228164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1228863 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1228229
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1228229
    | exact resolve eq1228229 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228229
  have eq1229881 : y = (k y (σ x)) := by
    first
    | exact superpose eq1228164 eq1226446
    | exact resolve eq1226446 eq1228164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226446 eq1228164
  have eq1230340 : (k y y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1229881 eq1069250
    | exact resolve eq1069250 eq1229881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1069250 eq1229881
  have eq1230484 : y = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1230340
       have i₂ := eq1226355
       grind)
    | exact superpose eq1226355 eq1230340
    | exact resolve eq1230340 eq1226355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226355 eq1230340
  have eq1230547 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1228863 eq1230484
    | exact resolve eq1230484 eq1228863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230484
  have eq1230603 : y = (τ (M.op (σ x) (σ y))) := by
    first
    | (have r₁ := eq1230547
       have r₂ := eq27
       grind)
    | exact resolve eq1230547 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230547
  have eq1230664 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1230603 eq15
    | exact resolve eq15 eq1230603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1230603
  have eq1231396 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1230664
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1230664
    | exact resolve eq1230664 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1230664
  have eq1231453 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1228863 eq1231396
    | exact resolve eq1231396 eq1228863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1228863 eq1231396
  have eq1231471 : False := by grind
  exact eq1231471

/-- `Equation731`: `x = y ◇ (y ◇ ((z ◇ z) ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_x_pyy_pyx_Equation731 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law731 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law731.models_iff G M).mp hM
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 (M.op (M.op X2 X2) X0))) = X0 := by
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
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
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
  have eq59 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) = (M.op X1 (M.op X1 X0)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (M.op (M.op X2 X2) (M.op (M.op X3 X3) X0)) X1 X2
       have i₂ := eq14 X0 (M.op X2 X2) X3
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X1 X1) X0) (M.op X2 X2) X2
       have i₂ := eq14 X0 (M.op X2 X2) X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq70 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq103 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (σ (k (M.op x y) (τ X0))) = (k (σ (M.op x y)) X0) := by
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
  have eq118 : (σ (k (M.op x y) x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq37 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq37
    | (have j0 := eq37 x
       grind)
    | exact resolve eq37 eq22
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
  have eq129 : (k (M.op x y) x) = (τ (k (σ (M.op x y)) (σ x))) := by
    first
    | exact superpose eq118 eq16
    | exact resolve eq16 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq120 eq16
    | exact resolve eq16 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq255 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq261 : ∀ X0 X1 : G, (σ (k (k (τ X0) X1) (M.op x y))) = (k (k X0 (σ X1)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq41 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq41
    | exact resolve eq41 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq414 : ∀ X0 : G, (k (τ X0) (k (M.op x y) x)) = (τ (k X0 (k (σ (M.op x y)) (σ x)))) := by
    intro X0
    first
    | exact superpose eq118 eq255
    | exact resolve eq255 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq419 : ∀ X0 : G, (k (τ X0) (M.op x y)) = (τ (k X0 (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq20 eq255
    | (have j0 := eq255 X0 (M.op x y)
       grind)
    | exact resolve eq255 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq460 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq103 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq103
    | (have j0 := eq103 (σ X0)
       grind)
    | exact resolve eq103 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq497 : (k (k (M.op x y) (M.op x y)) (M.op x y)) = (τ (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y)))) := by
    first
    | exact superpose eq142 eq419
    | exact resolve eq419 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq571 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X1)) = (M.op X4 (M.op X4 X1)) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq59 X1 X4 x x
       have i₂ := eq59 X1 X0 x x
       grind)
    | (have i₁ := eq59 X0 X1 x x
       have i₂ := eq59 X0 (M.op x x) x x
       grind)
    | exact superpose eq59 eq59
    | exact resolve eq59 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq588 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X4 X4) X1) = (M.op X2 (M.op X2 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq14 (M.op (M.op X4 X4) X1) X2 x
       have i₂ := eq59 X1 X0 x X4
       grind)
    | (have i₁ := eq14 (M.op (M.op X2 X2) X0) X1 X2
       have i₂ := eq59 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq589 : ∀ X0 X1 X2 : G, (M.op (M.op X2 X2) (M.op X0 (M.op X0 X1))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X2 X2) x
       have i₂ := eq59 X1 X0 X2 x
       grind)
    | (have i₁ := eq14 X0 (M.op X2 X2) X2
       have i₂ := eq59 X0 (M.op X2 X2) X2 x
       grind)
    | exact superpose eq59 eq14
    | exact resolve eq14 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq594 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) X2) = (M.op (M.op X0 (M.op X0 (M.op X1 X1))) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq60 X2 X3 (M.op (M.op X1 X1) (M.op X1 X1))
       have i₂ := eq59 (M.op X1 X1) X0 (M.op X1 X1) X1
       grind)
    | exact superpose eq59 eq60
    | exact resolve eq60 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq646 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X0 X1))) = (M.op X3 (M.op X3 (M.op X2 X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq571 X2 (M.op X2 X1) X3
       have i₂ := eq571 X2 X1 X0
       grind)
    | (have i₁ := eq571 X2 (M.op X2 X1) X3
       have i₂ := eq571 X0 X1 X2
       grind)
    | exact superpose eq571 eq571
    | exact resolve eq571 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq652 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op X0 (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq571 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq571
    | (have j0 := eq571 x y X0
       grind)
    | exact resolve eq571 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq653 : ∀ X0 : G, (M.op X0 (M.op X0 (σ y))) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq571
    | (have j0 := eq571 X0 (σ y) (σ x)
       grind)
    | exact resolve eq571 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq709 : ∀ X0 : G, y = (M.op (M.op X0 X0) (M.op x (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq14 y (M.op X0 X0) X0
       have i₂ := eq652 (M.op X0 X0)
       grind)
    | exact superpose eq652 eq14
    | exact resolve eq14 eq652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq652
  have eq723 : ∀ X0 X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X1 X1) (M.op (M.op X0 X0) (σ y))) := by
    intro X0 X1
    first
    | (have i₁ := eq653 (M.op x x)
       have i₂ := eq60 sF3 X1 x
       grind)
    | (have i₁ := eq653 (M.op X1 X1)
       have i₂ := eq60 sF3 X1 x
       grind)
    | exact superpose eq60 eq653
    | exact resolve eq653 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq731 : ∀ X0 : G, (σ y) = (M.op (M.op X0 X0) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq653 eq14
    | exact resolve eq14 eq653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq780 : ∀ X0 X1 X2 X3 : G, (M.op X3 X1) = (M.op (M.op X2 X2) (M.op X3 (M.op X0 (M.op X0 X1)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq589 X3 (M.op X3 X1) X2
       have i₂ := eq571 X3 X1 X0
       grind)
    | (have i₁ := eq589 X3 (M.op X3 X1) X2
       have i₂ := eq571 X0 X1 X3
       grind)
    | exact superpose eq571 eq589
    | exact resolve eq589 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq782 : ∀ X0 X1 X2 X3 X4 : G, (M.op X4 X2) = (M.op (M.op X3 X3) (M.op X4 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq589 X4 (M.op X4 X2) X3
       have i₂ := eq59 X2 X4 X0 X1
       grind)
    | (have i₁ := eq589 (M.op X2 X2) (M.op (M.op X3 X3) X0) X2
       have i₂ := eq59 X0 X1 X2 X3
       grind)
    | exact superpose eq59 eq589
    | exact resolve eq589 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq866 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq70 X1 X0
       grind)
    | (have i₁ := eq12 (σ X1) (σ X1)
       have i₂ := eq70 X0 X1
       grind)
    | exact superpose eq70 eq12
    | (have j0 := eq12 (σ X0) (σ X0)
       have j1 := eq70 X1 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq70 X0 X0
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq70 X0 X1
       grind)
    | exact resolve eq12 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq868 : ∀ X0 X1 X2 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X0)) = X2 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (σ X0)
       have i₂ := eq70 X1 X0
       grind)
    | (have i₁ := eq13 X0 (σ X0)
       have i₂ := eq70 X0 X0
       grind)
    | exact superpose eq70 eq13
    | (have j0 := eq13 X2 (σ X0)
       have j1 := eq70 X1 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq70 X0 X1
       grind)
    | exact resolve eq13 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq883 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq70 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq886 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq866 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq866
  have eq887 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq886 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886
  have eq890 : ∀ X0 X1 X2 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k X2 (σ X0)) = X2 ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq868 X0 X1 X2
       have j1 := eq13 X2 (σ X0)
       grind)
    | (have r₁ := eq868 X0 X1 X2
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq868 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq868
  have eq891 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq887 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq887
    | (have j0 := eq887 X0 X1
       grind)
    | exact resolve eq887 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887
  have eq1364 : ∀ X0 : G, (k (k X0 (σ (τ X0))) (σ (M.op x y))) = (σ (k (M.op (τ X0) (τ X0)) (M.op x y))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq261 X0 (τ X0)
       have i₂ := eq103 (τ X0)
       grind)
    | exact superpose eq103 eq261
    | (have j1 := eq103 (τ X0)
       grind)
    | exact resolve eq261 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq261
  have eq1388 : ∀ X0 : G, (σ (k (M.op (τ X0) (τ X0)) (M.op x y))) = (k (k X0 X0) (σ (M.op x y))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq1364 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1364
    | (have j0 := eq1364 X0
       grind)
    | exact resolve eq1364 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1364
  have eq3628 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ y)) = (M.op X1 (M.op X1 (M.op (σ x) (M.op (σ x) (σ y))))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq588
    | (have j0 := eq588 (σ x) (σ y) X1 X0
       grind)
    | exact resolve eq588 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3733 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X4 (M.op X4 X1))) = (M.op (M.op X2 X2) (M.op X3 (M.op (M.op X0 X0) X1))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq589 X3 (M.op X3 (M.op X4 (M.op X4 X1))) X2
       have i₂ := eq588 X4 X1 X3 X0
       grind)
    | exact superpose eq588 eq589
    | exact resolve eq589 eq588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq588
  have eq4140 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) X3) = (M.op (M.op X1 (M.op X0 (M.op X0 X1))) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq594 X1 X1 X3 X2
       have i₂ := eq571 X1 X1 X0
       grind)
    | (have i₁ := eq594 X1 X1 X3 X2
       have i₂ := eq571 X0 X1 X1
       grind)
    | exact superpose eq571 eq594
    | exact resolve eq594 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq594
  have eq5059 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq460 X0
       grind)
    | exact superpose eq460 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq460 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq460 X0
       grind)
    | exact resolve eq13 eq460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5084 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op X1 X1) (M.op (σ X0) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq589 (σ X0) (σ X0) X1
       have i₂ := eq460 X0
       grind)
    | exact superpose eq460 eq589
    | (have j1 := eq460 X0
       grind)
    | exact resolve eq589 eq460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5089 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq460 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq460
  have eq5091 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq5059 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq5059 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq5059 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5059
  have eq11175 : ∀ X0 X1 X2 : G, (σ X1) ≠ (M.op (σ X1) X0) ∨ (k X2 (σ X1)) = X2 ∨ (σ (k (τ X0) X1)) = (M.op (σ X1) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq890 X0 (τ X0) X2
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq890
    | (have j0 := eq890 X1 X1 X2
       grind)
    | exact resolve eq890 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq890
  have eq11264 : ∀ X0 X1 X2 : G, (σ X1) ≠ (M.op (σ X1) X0) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (k X2 (σ X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq11175 X0 X1 X2
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq11175
    | (have j0 := eq11175 X0 X1 X2
       grind)
    | exact resolve eq11175 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11175
  have eq15196 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5091 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq5091
    | (have j0 := eq5091 (τ X0) X1
       grind)
    | exact resolve eq5091 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq15203 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15196 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq15196
    | (have j0 := eq15196 X0 X1
       grind)
    | exact resolve eq15196 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15196
  have eq15209 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15203 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq15203
    | (have j0 := eq15203 X0 X1
       grind)
    | exact resolve eq15203 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15203
  have eq15215 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq891 X0 X1
       have j1 := eq883 X0 X1
       grind)
    | (have r₁ := eq891 X0 X1
       have r₂ := eq883 X0 X1
       grind)
    | (have r₁ := eq891 X1 X1
       have r₂ := eq883 X1 X1
       grind)
    | exact resolve eq891 eq883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq883 eq891
  have eq15226 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15215 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq15215
    | exact resolve eq15215 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15307 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq15215 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15215
    | (have j0 := eq15215 x X0
       grind)
    | exact resolve eq15215 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15470 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (σ X0))) = (M.op (σ X1) (σ (k X0 X1))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq571 (σ X1) (σ X0) X2
       have i₂ := eq15215 X1 X0
       grind)
    | exact superpose eq15215 eq571
    | (have j1 := eq15215 X1 X1
       grind)
    | exact resolve eq571 eq15215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15474 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (M.op X2 X2) (M.op (σ X1) (σ (k X0 X1)))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq589 (σ X1) (σ X0) X2
       have i₂ := eq15215 X1 X0
       grind)
    | exact superpose eq15215 eq589
    | (have j1 := eq15215 X1 X1
       grind)
    | exact resolve eq589 eq15215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq15486 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq15226 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq15226
    | (have j0 := eq15226 X0 X1
       grind)
    | exact resolve eq15226 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq15226
  have eq26114 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq15307 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq15307
    | (have j0 := eq15307 y
       grind)
    | exact resolve eq15307 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15307
  have eq26126 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq26114
       have i₂ := eq67
       grind)
    | exact superpose eq67 eq26114
    | exact resolve eq26114 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26114
  have eq26143 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq26126
    | exact resolve eq26126 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26126
  have eq26650 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15486 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq15486
    | (have j0 := eq15486 X1 X1
       grind)
    | exact resolve eq15486 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15486
  have eq27120 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq67
       have i₂ := eq26650 y x
       grind)
    | exact superpose eq26650 eq67
    | (have j1 := eq26650 x x
       grind)
    | exact resolve eq67 eq26650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq27360 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq27120
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq27120
    | exact resolve eq27120 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq27120
  have eq27370 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq27360
    | exact resolve eq27360 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27360
  have eq27384 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq27370 eq26143
    | exact resolve eq26143 eq27370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26143 eq27370
  have eq27391 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq27384
       have r₂ := eq27
       grind)
    | exact resolve eq27384 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27384
  have eq27413 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq27391 eq13
    | (have j0 := eq13 X0 (σ x)
       grind)
    | (have r₁ := eq13 X0 (σ x)
       have r₂ := eq27391
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq27391
       grind)
    | exact resolve eq13 eq27391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27391
  have eq27490 : ∀ X0 : G, x = (M.op x x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq27413 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27413
  have eq27990 : ∀ X0 X1 : G, x ≠ x ∨ (k X0 x) = X0 ∨ (k X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 x
       have i₂ := eq27490 X1
       grind)
    | exact superpose eq27490 eq13
    | (have j0 := eq13 X0 x
       have j1 := eq27490 X1
       grind)
    | (have r₁ := eq13 X0 x
       have r₂ := eq27490 X0
       grind)
    | exact resolve eq13 eq27490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27490
  have eq28067 : ∀ X0 X1 : G, (k X1 (σ x)) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq27990 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27990
  have eq28105 : ∀ X0 : G, (τ (σ x)) = (k x x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | (have i₁ := eq49
       have i₂ := eq28067 (k sF2 sF2) x
       grind)
    | exact superpose eq28067 eq49
    | (have j1 := eq28067 X0 x
       grind)
    | exact resolve eq49 eq28067
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq28067
  have eq28192 : ∀ X0 : G, x = (k x x) ∨ (k X0 x) = X0 := by
    intro X0
    first
    | exact superpose eq28 eq28105
    | (have j0 := eq28105 x
       grind)
    | exact resolve eq28105 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq28105
  have eq28228 : ∀ X0 : G, (k X0 x) = X0 := by
    intro X0
    first
    | (have j0 := eq28192 X0
       have j1 := eq15209 x X0
       grind)
    | (have r₁ := eq28192 X0
       have r₂ := eq15209 x x
       grind)
    | (have r₁ := eq28192 x
       have r₂ := eq15209 x x
       grind)
    | exact resolve eq28192 eq15209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15209 eq28192
  have eq28284 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq5091 x X0
       have i₂ := eq28228 x
       grind)
    | exact superpose eq28228 eq5091
    | (have j0 := eq5091 x X0
       grind)
    | exact resolve eq5091 eq28228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5091
  have eq28285 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq103 x
       have i₂ := eq28228 x
       grind)
    | exact superpose eq28228 eq103
    | (have j0 := eq103 x
       grind)
    | exact resolve eq103 eq28228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28310 : x = (M.op x x) := by grind
  clear eq28285
  have eq28311 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq28284 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28284
  have eq28332 : ∀ X0 : G, (k X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq28311 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28311
    | (have j0 := eq28311 X0
       grind)
    | exact resolve eq28311 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq28311
  have eq28394 : ∀ X0 X1 : G, (M.op X0 (M.op X0 (M.op x X1))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 x
       have i₂ := eq28310
       grind)
    | exact superpose eq28310 eq14
    | exact resolve eq14 eq28310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28397 : ∀ X0 X1 : G, (M.op (M.op X1 X1) X0) = (M.op x X0) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X1 x
       have i₂ := eq28310
       grind)
    | exact superpose eq28310 eq60
    | exact resolve eq60 eq28310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq28443 : y = (M.op x (M.op x (M.op x y))) := by
    first
    | (have i₁ := eq709 x
       have i₂ := eq28310
       grind)
    | exact superpose eq28310 eq709
    | exact resolve eq709 eq28310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq709
  have eq28545 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq28332 eq103
    | (have j0 := eq103 (σ x)
       grind)
    | exact resolve eq103 eq28332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28570 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq28545
  have eq29132 : (σ y) = (M.op (σ x) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq28570 eq731
    | exact resolve eq731 eq28570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28570
  have eq29939 : ∀ X0 : G, y = (M.op X0 (M.op X0 (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq28443
       have i₂ := eq571 x sF0 x
       grind)
    | (have i₁ := eq28443
       have i₂ := eq571 X0 sF0 x
       grind)
    | exact superpose eq571 eq28443
    | exact resolve eq28443 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28443
  have eq31960 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 X0) (σ y)) := by
    intro X0
    first
    | exact superpose eq29132 eq589
    | exact resolve eq589 eq29132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq589 eq29132
  have eq36072 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq31960 x
       have i₂ := eq28310
       grind)
    | exact superpose eq28310 eq31960
    | exact resolve eq31960 eq28310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28310
  have eq36163 : (M.op (σ x) (M.op (σ x) (σ y))) = (M.op x (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq36072 eq653
    | exact resolve eq653 eq36072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq42229 : ∀ X0 X1 X2 X3 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 X0) (M.op X1 (M.op X2 (M.op X2 X1)))) (M.op (M.op X3 X3) (σ y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq723 X3 (M.op X1 (M.op X2 (M.op X2 X1)))
       have i₂ := eq4140 X2 X1 X0 (M.op X1 (M.op X2 (M.op X2 X1)))
       grind)
    | exact superpose eq4140 eq723
    | exact resolve eq723 eq4140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq723
  have eq42231 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op (M.op X0 X0) (M.op X1 (M.op X2 (M.op X2 X1)))) (M.op (σ x) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq731 (M.op X1 (M.op X2 (M.op X2 X1)))
       have i₂ := eq4140 X2 X1 X0 (M.op X1 (M.op X2 (M.op X2 X1)))
       grind)
    | exact superpose eq4140 eq731
    | exact resolve eq731 eq4140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731 eq4140
  have eq42500 : ∀ X0 X1 X2 : G, (σ y) = (M.op (M.op (M.op X0 X0) (M.op X1 (M.op X2 (M.op X2 X1)))) (M.op x (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq36163 eq42231
    | exact resolve eq42231 eq36163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42231
  have eq42502 : ∀ X0 X1 X2 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op (M.op X0 X0) (M.op X1 (M.op X2 (M.op X2 X1)))) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | exact superpose eq31960 eq42229
    | exact resolve eq42229 eq31960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31960 eq42229
  have eq42841 : ∀ X1 : G, (σ y) = (M.op (M.op X1 X1) (M.op x (M.op (σ x) (σ y)))) := by
    intro X1
    first
    | (have i₁ := eq42500 x X1 x
       have i₂ := eq780 x X1 x X1
       grind)
    | exact superpose eq780 eq42500
    | exact resolve eq42500 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42500
  have eq42842 : ∀ X1 : G, (M.op (σ x) (M.op (σ x) (σ y))) = (M.op (M.op X1 X1) (M.op (σ x) (σ y))) := by
    intro X1
    first
    | (have i₁ := eq42502 x X1 x
       have i₂ := eq780 x X1 x X1
       grind)
    | exact superpose eq780 eq42502
    | exact resolve eq42502 eq780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq780 eq42502
  have eq42907 : ∀ X1 : G, (M.op (M.op X1 X1) (M.op (σ x) (σ y))) = (M.op x (M.op (σ x) (σ y))) := by
    intro X1
    first
    | exact superpose eq36163 eq42842
    | exact resolve eq42842 eq36163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36163 eq42842
  have eq43340 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op X0 (M.op (σ x) (σ y))))) = (M.op X0 (M.op (M.op X1 X1) (M.op x (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq42907 eq646
    | exact resolve eq646 eq42907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42907
  have eq43359 : ∀ X0 X2 : G, (M.op X0 (σ y)) = (M.op X2 (M.op X2 (M.op X0 (M.op (σ x) (σ y))))) := by
    intro X0 X2
    first
    | exact superpose eq42841 eq43340
    | exact resolve eq43340 eq42841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42841 eq43340
  have eq92619 : ∀ X0 X1 X2 X4 : G, (M.op X4 X2) = (M.op x (M.op X4 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)))) := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq782 X0 X1 X2 x X4
       have i₂ := eq28397 (M.op X4 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))) x
       grind)
    | exact superpose eq28397 eq782
    | exact resolve eq782 eq28397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq782
  have eq92620 : ∀ X1 X2 X4 : G, (M.op X4 X2) = (M.op x (M.op X4 (M.op x (M.op (M.op X1 X1) X2)))) := by
    intro X1 X2 X4
    first
    | (have i₁ := eq92619 x X1 X2 X4
       have i₂ := eq28397 (M.op (M.op X1 X1) X2) x
       grind)
    | exact superpose eq28397 eq92619
    | exact resolve eq92619 eq28397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92619
  have eq92621 : ∀ X2 X4 : G, (M.op X4 X2) = (M.op x (M.op X4 (M.op x (M.op x X2)))) := by
    intro X2 X4
    first
    | (have i₁ := eq92620 x X2 X4
       have i₂ := eq28397 X2 x
       grind)
    | exact superpose eq28397 eq92620
    | exact resolve eq92620 eq28397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92620
  have eq92838 : ∀ X0 X1 X2 : G, (M.op x (M.op X0 X1)) = (M.op X0 (M.op X2 (M.op X2 (M.op x (M.op x X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq646 X2 (M.op x (M.op x X1)) X0 x
       have i₂ := eq92621 X1 X0
       grind)
    | exact superpose eq92621 eq646
    | exact resolve eq646 eq92621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646 eq92621
  have eq92885 : ∀ X0 X1 : G, (M.op X0 (M.op x X1)) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq92838 X0 X1 x
       have i₂ := eq28394 x (M.op x X1)
       grind)
    | exact superpose eq28394 eq92838
    | exact resolve eq92838 eq28394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92838
  have eq158092 : ∀ X0 X1 X3 X4 : G, (M.op X3 (M.op X4 (M.op X4 X1))) = (M.op x (M.op X3 (M.op (M.op X0 X0) X1))) := by
    intro X0 X1 X3 X4
    first
    | (have i₁ := eq3733 X0 X1 x X3 X4
       have i₂ := eq28397 (M.op X3 (M.op (M.op X0 X0) X1)) x
       grind)
    | exact superpose eq28397 eq3733
    | exact resolve eq3733 eq28397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3733
  have eq158093 : ∀ X1 X3 X4 : G, (M.op X3 (M.op X4 (M.op X4 X1))) = (M.op x (M.op X3 (M.op x X1))) := by
    intro X1 X3 X4
    first
    | (have i₁ := eq158092 x X1 X3 X4
       have i₂ := eq28397 X1 x
       grind)
    | exact superpose eq28397 eq158092
    | exact resolve eq158092 eq28397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158092
  have eq158979 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op (σ x) (M.op (σ x) (σ y))))) = (M.op (M.op x (M.op (M.op X0 (M.op X0 X1)) (M.op x X1))) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq3628 (M.op X0 (M.op X0 X1)) X2
       have i₂ := eq158093 X1 (M.op X0 (M.op X0 X1)) X0
       grind)
    | exact superpose eq158093 eq3628
    | exact resolve eq3628 eq158093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3628 eq158093
  have eq159546 : ∀ X0 X1 X2 : G, (M.op X2 (M.op X2 (M.op (σ x) (M.op (σ x) (σ y))))) = (M.op (M.op x (M.op x (M.op (M.op X0 (M.op X0 X1)) X1))) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq158979 X0 X1 X2
       have i₂ := eq92885 (M.op X0 (M.op X0 X1)) X1
       grind)
    | exact superpose eq92885 eq158979
    | exact resolve eq158979 eq92885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158979
  have eq160416 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op x (M.op x (M.op (M.op X0 (M.op X0 X1)) X1))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq43359 eq159546
    | exact resolve eq159546 eq43359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43359 eq159546
  have eq160924 : ∀ X0 X1 : G, (M.op (σ x) (σ y)) = (M.op (M.op x (M.op x (M.op (M.op X0 (M.op X0 X1)) X1))) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq160416
    | (have j0 := eq160416 X0 X1
       grind)
    | exact resolve eq160416 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq160416
  have eq227959 : (k (k (k (σ (M.op x y)) (σ x)) (k (σ (M.op x y)) (σ x))) (σ (M.op x y))) = (σ (k (M.op (k (M.op x y) x) (k (M.op x y) x)) (M.op x y))) ∨ (k (M.op x y) x) = (M.op (k (M.op x y) x) (k (M.op x y) x)) := by
    first
    | exact superpose eq129 eq1388
    | exact resolve eq1388 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq1388
  have eq228150 : (σ (k (M.op (M.op x y) (M.op x y)) (M.op x y))) = (k (k (k (σ (M.op x y)) (σ x)) (k (σ (M.op x y)) (σ x))) (σ (M.op x y))) ∨ (k (M.op x y) x) = (M.op (k (M.op x y) x) (k (M.op x y) x)) := by
    first
    | (have i₁ := eq227959
       have i₂ := eq28228 sF0
       grind)
    | exact superpose eq28228 eq227959
    | exact resolve eq227959 eq28228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq227959
  have eq228190 : (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (σ (k (M.op (M.op x y) (M.op x y)) (M.op x y))) ∨ (k (M.op x y) x) = (M.op (k (M.op x y) x) (k (M.op x y) x)) := by
    first
    | exact superpose eq28332 eq228150
    | exact resolve eq228150 eq28332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228150
  have eq228222 : (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (σ (k (M.op (M.op x y) (M.op x y)) (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq228190
       have i₂ := eq28228 sF0
       grind)
    | exact superpose eq28228 eq228190
    | exact resolve eq228190 eq28228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28228 eq228190
  have eq230856 : ∀ X0 : G, (σ X0) = (M.op x (M.op (σ X0) (σ (k X0 X0)))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq5084 X0 x
       have i₂ := eq28397 (M.op (σ X0) (σ (k X0 X0))) x
       grind)
    | exact superpose eq28397 eq5084
    | (have j0 := eq5084 X0 x
       grind)
    | exact resolve eq5084 eq28397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5084
  have eq231073 : ∀ X0 : G, (σ X0) = (M.op x (σ (k (k X0 X0) X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq230856 X0
       have i₂ := eq15215 X0 (k X0 X0)
       grind)
    | exact superpose eq15215 eq230856
    | (have j0 := eq230856 X0
       have j1 := eq15215 X0 x
       grind)
    | exact resolve eq230856 eq15215
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15215 eq230856
  have eq231151 : ∀ X0 : G, (σ X0) = (M.op x (σ (k (k X0 X0) X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq231073 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231073
  have eq233977 : ∀ X0 X1 : G, (k (σ (M.op x y)) (σ x)) ≠ (M.op (k (σ (M.op x y)) (σ x)) X0) ∨ (k X0 (k (σ (M.op x y)) (σ x))) = (M.op (k (σ (M.op x y)) (σ x)) X0) ∨ (k X1 (k (σ (M.op x y)) (σ x))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq118 eq11264
    | exact resolve eq11264 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11264
  have eq234129 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) X0) ∨ (k X0 (k (σ (M.op x y)) (σ x))) = (M.op (k (σ (M.op x y)) (σ x)) X0) ∨ (k X1 (k (σ (M.op x y)) (σ x))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq28332 eq233977
    | (have j0 := eq233977 X0 X1
       grind)
    | exact resolve eq233977 eq28332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233977
  have eq234191 : ∀ X0 X1 : G, (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) X0) ∨ (k X1 (k (σ (M.op x y)) (σ x))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq28332 eq234129
    | (have j0 := eq234129 X0 X1
       grind)
    | exact resolve eq234129 eq28332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234129
  have eq234238 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op (σ (M.op x y)) X0) ∨ (k X0 (σ (M.op x y))) = (M.op (σ (M.op x y)) X0) ∨ (k X1 (σ (M.op x y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq28332 eq234191
    | (have j0 := eq234191 X0 X1
       grind)
    | exact resolve eq234191 eq28332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234191
  have eq234924 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ (τ X0)))) = (M.op (σ (k (M.op x y) x)) (σ (τ (k X0 (k (σ (M.op x y)) (σ x)))))) ∨ (σ (k (M.op x y) x)) = (M.op (σ (k (M.op x y) x)) (σ (k (M.op x y) x))) := by
    intro X0 X1
    first
    | exact superpose eq414 eq15470
    | (have j0 := eq15470 X0 (k (M.op x y) x) x
       grind)
    | exact resolve eq15470 eq414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq414 eq15470
  have eq235727 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ (τ X0)))) = (M.op (σ (k (M.op x y) x)) (k X0 (k (σ (M.op x y)) (σ x)))) ∨ (σ (k (M.op x y) x)) = (M.op (σ (k (M.op x y) x)) (σ (k (M.op x y) x))) := by
    intro X0 X1
    first
    | (have i₁ := eq234924 X0 X1
       have i₂ := eq15 (k X0 (k sF1 sF2))
       grind)
    | exact superpose eq15 eq234924
    | exact resolve eq234924 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234924
  have eq236217 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ (τ X0)))) = (M.op (σ (k (M.op x y) x)) (k X0 (σ (M.op x y)))) ∨ (σ (k (M.op x y) x)) = (M.op (σ (k (M.op x y) x)) (σ (k (M.op x y) x))) := by
    intro X0 X1
    first
    | exact superpose eq28332 eq235727
    | exact resolve eq235727 eq28332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235727
  have eq236613 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ (τ X0)))) = (M.op (k (σ (M.op x y)) (σ x)) (k X0 (σ (M.op x y)))) ∨ (σ (k (M.op x y) x)) = (M.op (σ (k (M.op x y) x)) (σ (k (M.op x y) x))) := by
    intro X0 X1
    first
    | exact superpose eq118 eq236217
    | exact resolve eq236217 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236217
  have eq236826 : ∀ X0 X1 : G, (M.op X1 (M.op X1 (σ (τ X0)))) = (M.op (σ (M.op x y)) (k X0 (σ (M.op x y)))) ∨ (σ (k (M.op x y) x)) = (M.op (σ (k (M.op x y) x)) (σ (k (M.op x y) x))) := by
    intro X0 X1
    first
    | exact superpose eq28332 eq236613
    | exact resolve eq236613 eq28332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236613
  have eq236955 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (σ (M.op x y)) (k X0 (σ (M.op x y)))) ∨ (σ (k (M.op x y) x)) = (M.op (σ (k (M.op x y) x)) (σ (k (M.op x y) x))) := by
    intro X0 X1
    first
    | (have i₁ := eq236826 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq236826
    | exact resolve eq236826 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236826
  have eq236998 : ∀ X0 X1 : G, (k (σ (M.op x y)) (σ x)) = (M.op (k (σ (M.op x y)) (σ x)) (k (σ (M.op x y)) (σ x))) ∨ (M.op X1 (M.op X1 X0)) = (M.op (σ (M.op x y)) (k X0 (σ (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq118 eq236955
    | (have j0 := eq236955 X0 X1
       grind)
    | exact resolve eq236955 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq236955
  have eq237024 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X0)) = (M.op (σ (M.op x y)) (k X0 (σ (M.op x y)))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0 X1
    first
    | exact superpose eq28332 eq236998
    | (have j0 := eq236998 X0 X1
       grind)
    | exact resolve eq236998 eq28332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28332 eq236998
  have eq237050 : ∀ X0 X1 : G, (σ X0) = (M.op x (M.op (σ X1) (σ (k X0 X1)))) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15474 X0 X1 x
       have i₂ := eq28397 (M.op (σ X1) (σ (k X0 X1))) x
       grind)
    | exact superpose eq28397 eq15474
    | (have j0 := eq15474 X0 X1 x
       grind)
    | exact resolve eq15474 eq28397
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15474 eq28397
  have eq237508 : ∀ X0 : G, (σ (M.op x y)) = (M.op x (M.op (σ (τ X0)) (k (σ (M.op x y)) X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | exact superpose eq111 eq237050
    | (have j0 := eq237050 X0 (τ X0)
       grind)
    | exact resolve eq237050 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq237050
  have eq237664 : ∀ X0 : G, (σ (M.op x y)) = (M.op x (M.op X0 (k (σ (M.op x y)) X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq237508 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq237508
    | (have j0 := eq237508 X0
       grind)
    | exact resolve eq237508 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237508
  have eq237937 : ∀ X0 : G, (σ (M.op x y)) = (M.op x (M.op X0 (k (σ (M.op x y)) X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | exact superpose eq20 eq237664
    | (have j0 := eq237664 X0
       grind)
    | exact resolve eq237664 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237664
  have eq238192 : ∀ X0 : G, (σ (M.op x y)) = (M.op x (M.op X0 (k (σ (M.op x y)) X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq237937 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq237937
    | (have j0 := eq237937 X0
       grind)
    | exact resolve eq237937 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237937
  have eq580594 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (M.op x (k (σ (M.op x y)) X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq238192 x
       have i₂ := eq92885 x (k sF1 x)
       grind)
    | (have i₁ := eq238192 X0
       have i₂ := eq92885 X0 (k sF1 X0)
       grind)
    | exact superpose eq92885 eq238192
    | (have j0 := eq238192 X0
       grind)
    | exact resolve eq238192 eq92885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92885 eq238192
  have eq800269 : ∀ X0 X1 X2 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X0 (M.op (M.op X1 (M.op X1 X2)) X2))) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq160924 X1 X2
       have i₂ := eq571 x (M.op (M.op X1 (M.op X1 X2)) X2) X0
       grind)
    | (have i₁ := eq160924 X1 X2
       have i₂ := eq571 X0 (M.op (M.op X1 (M.op X1 X2)) X2) x
       grind)
    | exact superpose eq571 eq160924
    | exact resolve eq160924 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571 eq160924
  have eq1428064 : (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq228222
       have i₂ := eq26650 (M.op sF0 sF0) sF0
       grind)
    | exact superpose eq26650 eq228222
    | (have j1 := eq26650 x (M.op x y)
       grind)
    | exact resolve eq228222 eq26650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228222
  have eq1428424 : (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op (M.op x y) (M.op x y)))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq1428064
  have eq1428443 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq29939 eq1428424
    | exact resolve eq1428424 eq29939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428424
  have eq1428461 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq1428443
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1428443
    | exact resolve eq1428443 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428443
  have eq1428474 : (τ (σ y)) = (k (k (M.op x y) (M.op x y)) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1428461 eq497
    | exact resolve eq497 eq1428461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497 eq1428461
  have eq1428491 : y = (k (k (M.op x y) (M.op x y)) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq29 eq1428474
    | exact resolve eq1428474 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1428474
  have eq1429072 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (k (M.op x (k (σ (M.op x y)) (σ (M.op x y)))) (σ (M.op x y))) ∨ (k X0 (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq580594 eq234238
    | (have j0 := eq234238 X0 X0
       have j1 := eq580594 (σ (M.op x y))
       grind)
    | (have r₁ := eq234238 (M.op x (k (σ (M.op x y)) (σ (M.op x y)))) x
       have r₂ := eq580594 (σ (M.op x y))
       grind)
    | (have r₁ := eq234238 (σ (M.op x y)) x
       have r₂ := eq580594 (σ (M.op x y))
       grind)
    | exact resolve eq234238 eq580594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq234238 eq580594
  have eq1429080 : ∀ X0 : G, (σ (M.op x y)) = (k (M.op x (k (σ (M.op x y)) (σ (M.op x y)))) (σ (M.op x y))) ∨ (k X0 (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq1429072 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429072
  have eq1429087 : ∀ X0 : G, (σ (M.op x y)) = (k (M.op x (k (σ (M.op x y)) (σ (M.op x y)))) (σ (M.op x y))) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq1429080 X0
       have j1 := eq13 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq1429080 X0
       have r₂ := eq13 X0 (σ (M.op x y))
       grind)
    | exact resolve eq1429080 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429080
  have eq1429210 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (M.op X0 (M.op x (k (σ (M.op x y)) (σ (M.op x y)))))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k X1 (σ (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq237024 X0 X1
       have i₂ := eq1429087 (k X0 sF1)
       grind)
    | exact superpose eq1429087 eq237024
    | (have j1 := eq1429087 X1
       grind)
    | exact resolve eq237024 eq1429087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237024 eq1429087
  have eq1429229 : ∀ X0 X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op X0 (M.op X0 (M.op x (k (σ (M.op x y)) (σ (M.op x y)))))) ∨ (k X1 (σ (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1429210 X0 X1
       have j1 := eq13 X1 (σ (M.op x y))
       grind)
    | (have r₁ := eq1429210 X0 X1
       have r₂ := eq13 X0 (σ (M.op x y))
       grind)
    | exact resolve eq1429210 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429210
  have eq1429235 : ∀ X1 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (k X1 (σ (M.op x y))) = X1 := by
    intro X1
    first
    | (have i₁ := eq1429229 x X1
       have i₂ := eq28394 x (k sF1 sF1)
       grind)
    | exact superpose eq28394 eq1429229
    | (have j0 := eq1429229 x X1
       grind)
    | exact resolve eq1429229 eq28394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28394 eq1429229
  have eq1429239 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq142
       have i₂ := eq1429235 (k sF1 sF1)
       grind)
    | exact superpose eq1429235 eq142
    | (have j1 := eq1429235 X0
       grind)
    | exact resolve eq142 eq1429235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429235
  have eq2196038 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1428491 eq231151
    | (have j0 := eq231151 (M.op x y)
       grind)
    | exact resolve eq231151 eq1428491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231151 eq1428491
  have eq2196451 : (σ (M.op x y)) = (M.op x (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq2196038
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2196038
    | exact resolve eq2196038 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2196038
  have eq2196634 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq36072 eq2196451
    | exact resolve eq2196451 eq36072
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36072 eq2196451
  have eq2196756 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq2196634
    | exact resolve eq2196634 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2196634
  have eq2196854 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have r₁ := eq2196756
       have r₂ := eq27
       grind)
    | exact resolve eq2196756 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2196756
  have eq2196917 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq20 eq2196854
    | exact resolve eq2196854 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2196854
  have eq2197091 : ∀ X0 : G, (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) ∨ (k X0 (σ (M.op x y))) = X0 ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2196917 eq1429239
    | (have j0 := eq1429239 X0
       grind)
    | exact resolve eq1429239 eq2196917
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1429239 eq2196917
  have eq2197517 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (k X0 (σ (M.op x y))) = X0 ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq30 eq2197091
    | (have j0 := eq2197091 X0
       grind)
    | exact resolve eq2197091 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2197091
  have eq2197589 : ∀ X0 : G, (M.op x y) = (k (M.op x y) (M.op x y)) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq2197517 X0
       have j1 := eq13 (M.op x y) (M.op x y)
       grind)
    | (have r₁ := eq2197517 X0
       have r₂ := eq13 X0 (M.op x y)
       grind)
    | exact resolve eq2197517 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2197517
  have eq2202497 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq5089 X0
       have i₂ := eq2197589 (k X0 X0)
       grind)
    | exact superpose eq2197589 eq5089
    | (have j0 := eq5089 (M.op x y)
       have j1 := eq2197589 X0
       grind)
    | exact resolve eq5089 eq2197589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5089 eq2197589
  have eq2202781 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq2202497 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202497
  have eq2202857 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | exact superpose eq20 eq2202781
    | (have j0 := eq2202781 X0
       grind)
    | exact resolve eq2202781 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202781
  have eq2202933 : ∀ X0 : G, (k X0 (σ (M.op x y))) = X0 := by
    intro X0
    first
    | (have j0 := eq2202857 X0
       have j1 := eq13 X0 (σ (M.op x y))
       grind)
    | (have r₁ := eq2202857 X0
       have r₂ := eq13 X0 (σ (M.op x y))
       grind)
    | exact resolve eq2202857 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202857
  have eq2203191 : (τ (σ (M.op x y))) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2202933 eq142
    | exact resolve eq142 eq2202933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq2203337 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2202933 eq103
    | (have j0 := eq103 (σ (M.op x y))
       grind)
    | exact resolve eq103 eq2202933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq2202933
  have eq2204125 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2203337
  have eq2204623 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq30 eq2203191
    | exact resolve eq2203191 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2203191
  have eq2205344 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (M.op X0 (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ (M.op x y))))) (σ y)) := by
    intro X0
    first
    | exact superpose eq2204125 eq800269
    | exact resolve eq800269 eq2204125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq800269
  have eq2205360 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq2205344 x
       have i₂ := eq14 sF1 x sF1
       grind)
    | exact superpose eq14 eq2205344
    | exact resolve eq2205344 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2205344
  have eq2206196 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2204623 eq26650
    | (have j0 := eq26650 x (M.op x y)
       grind)
    | exact resolve eq26650 eq2204623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26650 eq2204623
  have eq2206204 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by grind
  clear eq2206196
  have eq2210513 : y = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2206204 eq29939
    | exact resolve eq29939 eq2206204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29939
  have eq2211083 : y = (M.op x y) := by
    first
    | exact superpose eq2206204 eq2210513
    | exact resolve eq2210513 eq2206204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2206204 eq2210513
  have eq2211329 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2211083 eq20
    | exact resolve eq20 eq2211083
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2211083
  have eq2212061 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2211329
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2211329
    | exact resolve eq2211329 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2211329
  have eq2213030 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2212061 eq2205360
    | exact resolve eq2205360 eq2212061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2205360 eq2212061
  have eq2213033 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2204125 eq2213030
    | exact resolve eq2213030 eq2204125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2204125 eq2213030
  have eq2213274 : False := by grind
  exact eq2213274

/-- `Equation826`: `x = x ◇ ((x ◇ y) ◇ (y ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,Y) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxy_pxx_pyx_Equation826 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law826 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law826.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq570 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq581 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X0 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq570 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq570
  have eq582 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq581 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq581
  have eq696 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq582 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq699 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq696 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq696 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq696 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq696 X0 X1
       have r₂ := eq14 (M.op X0 X0) (M.op X1 X0)
       grind)
    | exact resolve eq696 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696
  have eq751 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq699 X1 (τ X0)
       grind)
    | exact superpose eq699 eq19
    | (have j1 := eq699 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq754 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq699 (σ X1) (σ X0)
       grind)
    | exact superpose eq699 eq15
    | (have j1 := eq699 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699
  have eq845 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq751 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq751
    | exact resolve eq751 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq751
  have eq897 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq845 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq845
    | (have j0 := eq845 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq845 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq845
  have eq1084 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq754 x y
       grind)
    | exact superpose eq754 eq16
    | (have j1 := eq754 x y
       grind)
    | exact resolve eq16 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq1115 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1084
       have i₂ := eq897 x y
       grind)
    | exact superpose eq897 eq1084
    | (have j1 := eq897 (σ x) (σ y)
       grind)
    | (have r₁ := eq1084
       have r₂ := eq897 x y
       grind)
    | (have r₁ := eq1084
       have r₂ := eq897 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1084
       have r₂ := eq897 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1084 eq897
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq897 eq1084
  have eq1116 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1115
  have eq1120 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1116
       grind)
    | exact superpose eq1116 eq10
    | exact resolve eq10 eq1116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq1162 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1120
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1120
    | exact resolve eq1120 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1120
  have eq1163 : x = y := by grind
  clear eq1162
  have eq1165 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1163
       grind)
    | exact superpose eq1163 eq16
    | exact resolve eq16 eq1163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1163
  have eq1166 : False := by grind
  exact eq1166

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_pyy_pxy_pyy_pxy_Equation837 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
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
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
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
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq60 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq61 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq60 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq67 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq57 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq57 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq57 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq57 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq197 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq67 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq204 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq197 X0 X1
       have j1 := eq61 X1 X0
       grind)
    | (have r₁ := eq197 X0 X0
       have r₂ := eq61 X0 X0
       grind)
    | (have r₁ := eq197 X1 X0
       have r₂ := eq61 X0 X1
       grind)
    | exact resolve eq197 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq197
  have eq474 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq204 (σ X0) (σ X1)
       grind)
    | exact superpose eq204 eq15
    | exact resolve eq15 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq481 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq474 X0 X1
       have i₂ := eq204 X0 X1
       grind)
    | exact superpose eq204 eq474
    | exact resolve eq474 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq474
  have eq484 : False := by grind
  exact eq484

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pxy_pxx_pxy_Equation837 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
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
  have eq52 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq55 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq52 X0 X1
       have i₂ := eq37 X1
       grind)
    | exact superpose eq37 eq52
    | (have j0 := eq52 X0 X1
       grind)
    | exact resolve eq52 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq78 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
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
  have eq163 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq55 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq55
    | exact resolve eq55 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq186 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq163 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq163
    | (have j0 := eq163 X0 X1
       grind)
    | exact resolve eq163 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq163
  have eq191 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op X0 (σ X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq186 X0 X1
       have j1 := eq78 X1 X0
       grind)
    | (have r₁ := eq186 X1 X0
       have r₂ := eq78 X0 X1
       grind)
    | (have r₁ := eq186 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq78 X0 X1
       grind)
    | exact resolve eq186 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq186
  have eq195 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq191 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq191
    | exact resolve eq191 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq200 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq191 (σ X0) X1
       grind)
    | exact superpose eq191 eq15
    | (have j1 := eq191 (M.op (σ X0) (σ X1)) (k X0 X1)
       grind)
    | exact resolve eq15 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq209 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq195 X1 (τ X0)
       grind)
    | exact superpose eq195 eq18
    | (have j1 := eq195 (k X0 (σ X1)) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq18 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq195
  have eq530 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq209 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq209
    | exact resolve eq209 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq572 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq530 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq530
    | (have j0 := eq530 (σ (k X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq530 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq1247 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq200 x y
       grind)
    | exact superpose eq200 eq16
    | (have j1 := eq200 x y
       grind)
    | exact resolve eq16 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq1341 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1247
       have i₂ := eq572 x y
       grind)
    | exact superpose eq572 eq1247
    | (have j1 := eq572 (σ x) (σ y)
       grind)
    | (have r₁ := eq1247
       have r₂ := eq572 x y
       grind)
    | (have r₁ := eq1247
       have r₂ := eq572 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq1247
       have r₂ := eq572 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq1247 eq572
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572 eq1247
  have eq1342 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1341
  have eq1346 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1342
       grind)
    | exact superpose eq1342 eq10
    | exact resolve eq10 eq1342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1342
  have eq1392 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1346
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1346
    | exact resolve eq1346 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1346
  have eq1393 : x = y := by grind
  clear eq1392
  have eq1401 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1393
       grind)
    | exact superpose eq1393 eq16
    | exact resolve eq16 eq1393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393
  have eq1402 : False := by grind
  exact eq1402

/-- `Equation837`: `x = x ◇ ((y ◇ x) ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pxy_pxx_pxy_Equation837 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law837 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law837.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq49 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq89 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X0) X1) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq116 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq49 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq49
    | exact resolve eq49 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq127 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq116 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq116
    | (have j0 := eq116 X0
       grind)
    | exact resolve eq116 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq116
  have eq129 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq127 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq127
    | (have j0 := eq127 X0
       grind)
    | exact resolve eq127 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq130 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq129 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq129 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq129 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq133 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq130 (σ X0)
       grind)
    | exact superpose eq130 eq15
    | exact resolve eq15 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq146 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq133 X0
       have i₂ := eq130 X0
       grind)
    | exact superpose eq130 eq133
    | exact resolve eq133 eq130
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq130 eq133
  have eq241 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq84 x y
       grind)
    | exact superpose eq84 eq16
    | (have j1 := eq84 x y
       grind)
    | exact resolve eq16 eq84
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq1282 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq89 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq89
    | exact resolve eq89 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89
  have eq1326 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1282 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1282
    | (have j0 := eq1282 X0 X1
       grind)
    | exact resolve eq1282 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1282
  have eq2427 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq241
       have i₂ := eq1326 y x
       grind)
    | exact superpose eq1326 eq241
    | (have j1 := eq1326 (σ x) (σ y)
       grind)
    | (have r₁ := eq241
       have r₂ := eq1326 y x
       grind)
    | (have r₁ := eq241
       have r₂ := eq1326 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq241
       have r₂ := eq1326 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq241 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2428 : x = y ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq2427
  have eq27225 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2428
       grind)
    | exact superpose eq2428 eq16
    | exact resolve eq16 eq2428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2428
  have eq27226 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq27225
       have r₂ := eq146 x
       grind)
    | exact resolve eq27225 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27225
  have eq27229 : x ≠ x ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq27226
       grind)
    | exact superpose eq27226 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq27226
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq27226
       grind)
    | exact resolve eq12 eq27226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27226
  have eq27277 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq27229
  have eq27709 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq241
       have i₂ := eq27277
       grind)
    | exact superpose eq27277 eq241
    | exact resolve eq241 eq27277
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq241 eq27277
  have eq27746 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq27709
  have eq27747 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq27746
  have eq28006 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ x) (σ y)
       have i₂ := eq27747
       grind)
    | exact superpose eq27747 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq27747
       grind)
    | exact resolve eq12 eq27747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27747
  have eq28055 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq28006
  have eq28076 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq28055
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq28055
    | exact resolve eq28055 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28055
  have eq28099 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28076
       grind)
    | exact superpose eq28076 eq16
    | exact resolve eq16 eq28076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28076
  have eq28441 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq28099
       have i₂ := eq1326 y x
       grind)
    | exact superpose eq1326 eq28099
    | (have j1 := eq1326 (σ x) (σ y)
       grind)
    | (have r₁ := eq28099
       have r₂ := eq1326 y x
       grind)
    | (have r₁ := eq28099
       have r₂ := eq1326 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq28099
       have r₂ := eq1326 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq28099 eq1326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1326
  have eq28442 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq28441
  have eq28446 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq28442
       grind)
    | exact superpose eq28442 eq16
    | exact resolve eq16 eq28442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28442
  have eq28447 : x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq28446
       have r₂ := eq146 x
       grind)
    | exact resolve eq28446 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28446
  have eq28822 : x ≠ x ∨ (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq28447
       grind)
    | exact superpose eq28447 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq28447
       grind)
    | exact resolve eq12 eq28447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28447
  have eq28870 : (M.op x y) = (k x y) ∨ (σ x) = (σ y) := by grind
  clear eq28822
  have eq29246 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq28099
       have i₂ := eq28870
       grind)
    | exact superpose eq28870 eq28099
    | exact resolve eq28099 eq28870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28099 eq28870
  have eq29286 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq29246
  have eq29287 : (σ x) = (σ y) := by grind
  clear eq29286
  have eq29288 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29287
       grind)
    | exact superpose eq29287 eq16
    | exact resolve eq16 eq29287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29289 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq29287
       grind)
    | exact superpose eq29287 eq10
    | exact resolve eq10 eq29287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29287
  have eq29412 : x = y := by
    first
    | (have i₁ := eq29289
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq29289
    | exact resolve eq29289 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29289
  have eq29413 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq29288
       have i₂ := eq146 x
       grind)
    | exact superpose eq146 eq29288
    | exact resolve eq29288 eq146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq146 eq29288
  have eq29418 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq29413
       have i₂ := eq29412
       grind)
    | exact superpose eq29412 eq29413
    | exact resolve eq29413 eq29412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29412 eq29413
  have eq29419 : False := by grind
  exact eq29419
