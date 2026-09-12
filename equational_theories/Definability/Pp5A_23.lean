import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_pyx_pxx_pyx_Equation3008 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq28 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : x = (τ (σ x)) := by
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
  have eq32 : y = (τ (σ y)) := by
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
  have eq40 : ∀ X0 : G, (σ (k X0 x)) = (k (σ X0) (σ x)) := by
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
  have eq176 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq16 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq534 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       have i₂ := eq176 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       grind)
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq713 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq16 X3 (M.op X0 (M.op X1 X1)) x
       have i₂ := eq534 X0 X1 x
       grind)
    | exact superpose eq534 eq16
    | exact resolve eq16 eq534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq534
  have eq1565 : (M.op x x) = (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq28 y x
       grind)
    | exact superpose eq28 eq18
    | (have j1 := eq28 y x
       grind)
    | exact resolve eq18 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1569 : (M.op (σ x) (σ x)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq26
       have i₂ := eq28 sF3 sF2
       grind)
    | exact superpose eq28 eq26
    | (have j1 := eq28 (σ y) (σ x)
       grind)
    | exact resolve eq26 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq1680 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1684 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1680 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq1680 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq1680 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1680
  have eq4720 : ∀ X0 : G, x = (M.op (M.op x x) (M.op y (M.op X0 X0))) ∨ (M.op x y) = (k y x) := by
    intro X0
    first
    | (have i₁ := eq713 y X0 x
       have i₂ := eq1565
       grind)
    | exact superpose eq1565 eq713
    | exact resolve eq713 eq1565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1565
  have eq4722 : (M.op x y) = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq4720 x
       have i₂ := eq176 x y x
       grind)
    | exact superpose eq176 eq4720
    | exact resolve eq4720 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4720
  have eq4742 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ x)) (M.op (σ y) (M.op X0 X0))) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq1569 eq713
    | exact resolve eq713 eq1569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713 eq1569
  have eq4744 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq4742 x
       have i₂ := eq176 sF2 sF3 x
       grind)
    | exact superpose eq176 eq4742
    | exact resolve eq4742 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq4742
  have eq4757 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq4722
       grind)
    | exact superpose eq4722 eq40
    | exact resolve eq40 eq4722
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4722
  have eq4758 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq4757
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4757
    | exact resolve eq4757 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4757
  have eq4760 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq20 eq4758
    | exact resolve eq4758 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4758
  have eq4768 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq4760 eq4744
    | exact resolve eq4744 eq4760
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4744 eq4760
  have eq4775 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq4768
       have r₂ := eq27
       grind)
    | exact resolve eq4768 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4768
  have eq4780 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq4775 eq32
    | exact resolve eq32 eq4775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32 eq4775
  have eq4800 : x = y ∨ x = y := by
    first
    | exact superpose eq30 eq4780
    | exact resolve eq4780 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq4780
  have eq4801 : x = y := by grind
  clear eq4800
  have eq4804 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq4801
       grind)
    | exact superpose eq4801 eq18
    | exact resolve eq18 eq4801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq4805 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq4801
       grind)
    | exact superpose eq4801 eq24
    | exact resolve eq24 eq4801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq4801
  have eq4810 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq4805
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4805
    | exact resolve eq4805 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4805
  have eq4811 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq4804
       have i₂ := eq1684 x
       grind)
    | exact superpose eq1684 eq4804
    | exact resolve eq4804 eq1684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4804
  have eq4812 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq4810 eq26
    | exact resolve eq26 eq4810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq4810
  have eq4833 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4812
       have i₂ := eq1684 sF2
       grind)
    | exact superpose eq1684 eq4812
    | exact resolve eq4812 eq1684
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1684 eq4812
  have eq4837 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq4811
       grind)
    | exact superpose eq4811 eq40
    | exact resolve eq40 eq4811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4811
  have eq4892 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq4837
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4837
    | exact resolve eq4837 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq4837
  have eq4907 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4833 eq4892
    | exact resolve eq4892 eq4833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4833 eq4892
  have eq4913 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq4907
    | exact resolve eq4907 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq4907
  have eq4915 : False := by grind
  exact eq4915

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pxy_pyy_pyx_Equation3008 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq50 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq14 (M.op X0 X0) X1 X2
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
  have eq80 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq67
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq67
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq67 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq86 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq80
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq80
    | exact resolve eq80 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq87 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq86
    | exact resolve eq86 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq88 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
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
  have eq102 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq102 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq102 x
       have r₂ := eq13 X0 x
       grind)
    | exact resolve eq102 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq105 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq103 (σ X0)
       grind)
    | exact superpose eq103 eq10
    | exact resolve eq10 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq103 sF2
       grind)
    | exact superpose eq103 eq49
    | exact resolve eq49 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq109 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq108
       have i₂ := eq103 x
       grind)
    | exact superpose eq103 eq108
    | exact resolve eq108 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq112 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq105 X0
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq105
    | exact resolve eq105 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq129 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq132 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq129
       have i₂ := eq103 sF1
       grind)
    | exact superpose eq103 eq129
    | exact resolve eq129 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq135 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq132
       have i₂ := eq103 sF0
       grind)
    | exact superpose eq103 eq132
    | exact resolve eq132 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq153 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq135 eq36
    | exact resolve eq36 eq135
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq135
  have eq258 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq103 (τ X0)
       grind)
    | exact superpose eq103 eq34
    | exact resolve eq34 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq269 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq258 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq258
    | exact resolve eq258 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq271 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq269 X0
       have i₂ := eq103 X0
       grind)
    | exact superpose eq103 eq269
    | exact resolve eq269 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq269
  have eq367 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq51 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq51 eq51
    | exact resolve eq51 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq369 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       have i₂ := eq14 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X2 X2)) (M.op X1 X1) X1
       have i₂ := eq51 (M.op X1 X1) X0 X2
       grind)
    | exact superpose eq51 eq14
    | exact resolve eq14 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq433 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 X1 x (M.op X0 X0) X2
       have i₂ := eq51 x (M.op X0 X0) X0
       grind)
    | exact superpose eq51 eq50
    | exact resolve eq50 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq621 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (M.op (τ X0) (τ X0))
       have i₂ := eq271 X0
       grind)
    | exact superpose eq271 eq16
    | exact resolve eq16 eq271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq913 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq367 (M.op X0 X0) x X1
       have i₂ := eq51 x (M.op X0 X0) X0
       grind)
    | exact superpose eq51 eq367
    | exact resolve eq367 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq970 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq913 X1 (σ X0)
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq913
    | exact resolve eq913 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq972 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq913 X1 (τ X0)
       have i₂ := eq621 X0
       grind)
    | exact superpose eq621 eq913
    | exact resolve eq913 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq913
  have eq1097 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op X0 (M.op X1 X1))) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq14 X3 (M.op X0 (M.op X1 X1)) x
       have i₂ := eq369 X0 X1 x
       grind)
    | exact superpose eq369 eq14
    | exact resolve eq14 eq369
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1189 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op X1 X1)) ∨ (M.op X2 (M.op X0 X0)) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 X0)
       have i₂ := eq370 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq13 X2 (M.op X0 X0)
       have i₂ := eq370 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq370 eq13
    | (have j0 := eq13 X2 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq1219 : ∀ X0 X2 : G, (M.op X2 (M.op X0 X0)) = (k X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have j0 := eq1189 X0 x X2
       grind)
    | (have r₁ := eq1189 x X0 X2
       have r₂ := eq367 X0 x x
       grind)
    | (have r₁ := eq1189 (M.op X0 X0) (M.op X0 X0) X2
       have r₂ := eq367 X0 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq1189 eq367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq367 eq1189
  have eq1517 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 X0) x)) := by
    intro X0
    first
    | (have i₁ := eq433 X0 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq433
    | (have j0 := eq433 X0 x y
       grind)
    | exact resolve eq433 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1518 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq433
    | (have j0 := eq433 X0 (σ x) (σ y)
       grind)
    | exact resolve eq433 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq1673 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1517 (M.op x (M.op X0 X0))
       have i₂ := eq14 (M.op x (M.op X0 X0)) x X0
       grind)
    | exact superpose eq14 eq1517
    | exact resolve eq1517 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1693 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1518 (M.op sF2 (M.op x x))
       have i₂ := eq14 (M.op sF2 (M.op x x)) sF2 x
       grind)
    | exact superpose eq14 eq1518
    | exact resolve eq1518 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1518
  have eq2021 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1673 x
       have i₂ := eq972 X0 x
       grind)
    | exact superpose eq972 eq1673
    | exact resolve eq1673 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1673
  have eq2042 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (τ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1693 x
       have i₂ := eq972 X0 x
       grind)
    | exact superpose eq972 eq1693
    | exact resolve eq1693 eq972
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq972
  have eq2043 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1693 x
       have i₂ := eq970 X0 x
       grind)
    | exact superpose eq970 eq1693
    | exact resolve eq1693 eq970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq970 eq1693
  have eq7915 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op X1 (τ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1097 X1 (τ X0) X2
       have i₂ := eq621 X0
       grind)
    | exact superpose eq621 eq1097
    | exact resolve eq1097 eq621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq621 eq1097
  have eq15515 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq153
       have i₂ := eq1219 sF1 sF3
       grind)
    | exact superpose eq1219 eq153
    | exact resolve eq153 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq15516 : (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op y (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq15515
       have i₂ := eq1219 sF0 y
       grind)
    | exact superpose eq1219 eq15515
    | exact resolve eq15515 eq1219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1219 eq15515
  have eq50780 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq88 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88
  have eq50781 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq50780
    | exact resolve eq50780 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50780
  have eq50792 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq50781
       have r₂ := eq27
       grind)
    | exact resolve eq50781 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50781
  have eq50796 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq50792
    | exact resolve eq50792 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50792
  have eq51006 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (τ (M.op X0 X0)))) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    intro X0
    first
    | exact superpose eq50796 eq7915
    | exact resolve eq7915 eq50796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50796
  have eq51010 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2042 eq51006
    | exact resolve eq51006 eq2042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2042 eq51006
  have eq51022 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq51010 eq109
    | exact resolve eq109 eq51010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51010
  have eq51277 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq51022
    | exact resolve eq51022 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51022
  have eq51278 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by grind
  clear eq51277
  have eq51814 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x (τ (M.op X0 X0)))) ∨ (σ x) = (σ y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq7915 X0 x x
       have i₂ := eq51278
       grind)
    | exact superpose eq51278 eq7915
    | exact resolve eq7915 eq51278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7915 eq51278
  have eq51818 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2021 eq51814
    | exact resolve eq51814 eq2021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2021 eq51814
  have eq52000 : y = (M.op (M.op x y) (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1517 x
       have i₂ := eq51818
       grind)
    | exact superpose eq51818 eq1517
    | exact resolve eq1517 eq51818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1517
  have eq52022 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2043 x
       have i₂ := eq51818
       grind)
    | exact superpose eq51818 eq2043
    | exact resolve eq2043 eq51818
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2043 eq51818
  have eq52112 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq52022
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq52022
    | exact resolve eq52022 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52022
  have eq274905 : ∀ X0 : G, (M.op x y) = (M.op y (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq52000 eq369
    | exact resolve eq369 eq52000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52000
  have eq279211 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq52112 eq369
    | exact resolve eq369 eq52112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq369 eq52112
  have eq342538 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15516
       have i₂ := eq274905 sF0
       grind)
    | exact superpose eq274905 eq15516
    | exact resolve eq15516 eq274905
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15516 eq274905
  have eq342655 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq20 eq342538
    | exact resolve eq342538 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq342538
  have eq502018 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq342655 eq279211
    | exact resolve eq279211 eq342655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq279211 eq342655
  have eq502081 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq502018
  have eq502126 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq502081
       have r₂ := eq27
       grind)
    | exact resolve eq502081 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502081
  have eq502132 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq502126 eq29
    | exact resolve eq29 eq502126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq502126
  have eq502299 : x = y ∨ x = y := by
    first
    | exact superpose eq28 eq502132
    | exact resolve eq502132 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq502132
  have eq502300 : x = y := by grind
  clear eq502299
  have eq502321 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq502300
       grind)
    | exact superpose eq502300 eq18
    | exact resolve eq18 eq502300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq502322 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq502300
       grind)
    | exact superpose eq502300 eq24
    | exact resolve eq24 eq502300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq502300
  have eq502650 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq502322
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq502322
    | exact resolve eq502322 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq502322
  have eq502701 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq502650 eq26
    | exact resolve eq26 eq502650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq502650
  have eq503763 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq502701 eq109
    | exact resolve eq109 eq502701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq109 eq502701
  have eq504434 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq503763
       have i₂ := eq502321
       grind)
    | exact superpose eq502321 eq503763
    | exact resolve eq503763 eq502321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq502321 eq503763
  have eq504480 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq504434 eq15
    | exact resolve eq15 eq504434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq504434
  have eq504973 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq504480
    | exact resolve eq504480 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq504480
  have eq505114 : False := by grind
  exact eq505114

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pxy_pxx_pyx_Equation3008 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ a ≠ b ∨ k a b = M.op a a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq14 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq71 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq73 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq71 (σ X0)
       grind)
    | exact superpose eq71 eq10
    | exact resolve eq10 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq50
       have i₂ := eq71 sF2
       grind)
    | exact superpose eq71 eq50
    | exact resolve eq50 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq76 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq75
       have i₂ := eq71 x
       grind)
    | exact superpose eq71 eq75
    | exact resolve eq75 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq78 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq73 X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq73
    | exact resolve eq73 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq68
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq68
    | (have j1 := eq11 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq68 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq93
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq93
    | exact resolve eq93 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq21 eq98
    | exact resolve eq98 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq126 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq129 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq126
       have i₂ := eq71 sF1
       grind)
    | exact superpose eq71 eq126
    | exact resolve eq126 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq131 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq129
       have i₂ := eq71 sF0
       grind)
    | exact superpose eq71 eq129
    | exact resolve eq129 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq129
  have eq148 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (k (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq131 eq37
    | exact resolve eq37 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq131
  have eq473 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X1) (M.op X2 (σ (M.op X0 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 X2 (σ X0)
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq52
    | exact resolve eq52 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq474 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq52 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq52 eq52
    | exact resolve eq52 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq476 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       have i₂ := eq14 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq477 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X1)) = (M.op X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 (M.op X2 X2)) (M.op X1 X1) X1
       have i₂ := eq52 (M.op X1 X1) X0 X2
       grind)
    | exact superpose eq52 eq14
    | exact resolve eq14 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq51
    | (have j0 := eq51 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq51 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq587 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1 x (M.op X0 X0) X2
       have i₂ := eq52 x (M.op X0 X0) X0
       grind)
    | exact superpose eq52 eq51
    | exact resolve eq51 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq52
  have eq1114 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op X0 X0) (M.op X1 X1)) ∨ (M.op X2 (M.op X0 X0)) = (k X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 X0)
       have i₂ := eq477 (M.op X0 X0) X0 X1
       grind)
    | (have i₁ := eq13 X2 (M.op X0 X0)
       have i₂ := eq477 (M.op X0 X0) X1 X0
       grind)
    | exact superpose eq477 eq13
    | (have j0 := eq13 X2 (M.op X0 X0)
       grind)
    | exact resolve eq13 eq477
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq477
  have eq1143 : ∀ X0 X2 : G, (M.op X2 (M.op X0 X0)) = (k X2 (M.op X0 X0)) := by
    intro X0 X2
    first
    | (have j0 := eq1114 X0 x X2
       grind)
    | (have r₁ := eq1114 x X0 X2
       have r₂ := eq474 X0 x x
       grind)
    | (have r₁ := eq1114 (M.op X0 X0) (M.op X0 X0) X2
       have r₂ := eq474 X0 X0 (M.op (M.op X0 X0) (M.op X0 X0))
       grind)
    | exact resolve eq1114 eq474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq474 eq1114
  have eq1420 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 X0) x)) := by
    intro X0
    first
    | (have i₁ := eq587 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq587
    | (have j0 := eq587 X0 x y
       grind)
    | exact resolve eq587 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq587
  have eq2247 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ (M.op X0 X0)) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq580 x (σ (M.op X0 X0))
       have i₂ := eq473 X0 x (σ (M.op X0 X0))
       grind)
    | exact superpose eq473 eq580
    | exact resolve eq580 eq473
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq473 eq580
  have eq15920 : (σ (k y (M.op (M.op x y) (M.op x y)))) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | (have i₁ := eq148
       have i₂ := eq1143 sF1 sF3
       grind)
    | exact superpose eq1143 eq148
    | exact resolve eq148 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq15921 : (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) = (σ (M.op y (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq15920
       have i₂ := eq1143 sF0 y
       grind)
    | exact superpose eq1143 eq15920
    | exact resolve eq15920 eq1143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1143 eq15920
  have eq25032 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq25033 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq27 eq25032
    | exact resolve eq25032 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25032
  have eq25038 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq25033
       have r₂ := eq28
       grind)
    | exact resolve eq25033 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25033
  have eq25042 : (τ (σ x)) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq25038 eq76
    | exact resolve eq76 eq25038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25038
  have eq25204 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op x x) := by
    first
    | exact superpose eq29 eq25042
    | exact resolve eq25042 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25042
  have eq25205 : x = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq25204
  have eq25302 : y = (M.op (M.op x y) (M.op x x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1420 x
       have i₂ := eq25205
       grind)
    | exact superpose eq25205 eq1420
    | exact resolve eq1420 eq25205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1420
  have eq25327 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2247 x
       have i₂ := eq25205
       grind)
    | exact superpose eq25205 eq2247
    | exact resolve eq2247 eq25205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2247 eq25205
  have eq25358 : (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq25327
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq25327
    | exact resolve eq25327 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25327
  have eq152302 : ∀ X0 : G, (M.op x y) = (M.op y (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq25302 eq476
    | exact resolve eq476 eq25302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25302
  have eq152593 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ y) (M.op X0 X0)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq25358 eq476
    | exact resolve eq476 eq25358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476 eq25358
  have eq199787 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq15921
       have i₂ := eq152302 sF0
       grind)
    | exact superpose eq152302 eq15921
    | exact resolve eq15921 eq152302
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15921 eq152302
  have eq199870 : (σ (M.op x y)) = (M.op (σ y) (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq21 eq199787
    | exact resolve eq199787 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199787
  have eq229708 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq199870 eq152593
    | exact resolve eq152593 eq199870
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152593 eq199870
  have eq229745 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq229708
  have eq229761 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq229745
       have r₂ := eq28
       grind)
    | exact resolve eq229745 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229745
  have eq230116 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq229761 eq30
    | exact resolve eq30 eq229761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq229761
  have eq230187 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq230116
    | exact resolve eq230116 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq230116
  have eq230188 : x = y := by grind
  clear eq230187
  have eq230197 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq230188
       grind)
    | exact superpose eq230188 eq19
    | exact resolve eq19 eq230188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq230198 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq230188
       grind)
    | exact superpose eq230188 eq25
    | exact resolve eq25 eq230188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq230188
  have eq230410 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq230198
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq230198
    | exact resolve eq230198 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq230198
  have eq230439 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq230410 eq27
    | exact resolve eq27 eq230410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq230410
  have eq231547 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq230439 eq76
    | exact resolve eq76 eq230439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq230439
  have eq232014 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq231547
       have i₂ := eq230197
       grind)
    | exact superpose eq230197 eq231547
    | exact resolve eq231547 eq230197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230197 eq231547
  have eq232016 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq232014 eq15
    | exact resolve eq15 eq232014
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232014
  have eq232224 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq232016
    | exact resolve eq232016 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq232016
  have eq232288 : False := by grind
  exact eq232288

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(X,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pxy_pxx_pyy_pxy_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op a b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op a b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq174 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq16 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (k X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq176 X0 X1 X2
       have i₂ := eq174 X2
       grind)
    | exact superpose eq174 eq176
    | exact resolve eq176 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176
  have eq179 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) (M.op X1 (k X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq177 X0 X1 X2
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq177
    | exact resolve eq177 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq181 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (k X0 X0)) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 X1 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq16
    | exact resolve eq16 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X2) (k X1 X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16 X2 (k X1 X1) (k X0 X0)
       have i₂ := eq179 X1 (k X0 X0) X0
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179
  have eq568 : ∀ X0 X1 X3 : G, (M.op (M.op X0 X3) (M.op (k X1 X1) X0)) = X3 := by
    intro X0 X1 X3
    first
    | (have i₁ := eq181 x (M.op (k X1 X1) X0) X3
       have i₂ := eq543 X1 x X0
       grind)
    | exact superpose eq543 eq181
    | exact resolve eq181 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq543
  have eq1579 : ∀ X0 X1 : G, (M.op (k X0 X0) (M.op (k X1 X1) X0)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq568 X0 X1 X0
       have i₂ := eq174 X0
       grind)
    | exact superpose eq174 eq568
    | exact resolve eq568 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1588 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (k X0 X0) x)) := by
    intro X0
    first
    | (have i₁ := eq568 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq568
    | (have j0 := eq568 x X0 y
       grind)
    | exact resolve eq568 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1589 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (k X0 X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq26 eq568
    | (have j0 := eq568 (σ x) X0 (σ y)
       grind)
    | exact resolve eq568 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq1625 : (M.op x y) = (k x y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq1626 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1664 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq1626
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq1626
    | exact resolve eq1626 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1626
  have eq1665 : (M.op x y) = (k x y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq1625
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq1625
    | exact resolve eq1625 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1625
  have eq3782 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq1665
       grind)
    | exact superpose eq1665 eq40
    | exact resolve eq40 eq1665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq1665
  have eq3783 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have i₁ := eq3782
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3782
    | exact resolve eq3782 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3782
  have eq3785 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq20 eq3783
    | exact resolve eq3783 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3783
  have eq14231 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq3785 eq1664
    | exact resolve eq1664 eq3785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1664 eq3785
  have eq14241 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | (have r₁ := eq14231
       have r₂ := eq27
       grind)
    | exact resolve eq14231 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14231
  have eq14512 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (k X0 X0) (σ x))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq14241 eq1579
    | exact resolve eq1579 eq14241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14241
  have eq14611 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (k x x) ∨ x = y := by
    first
    | exact superpose eq1589 eq14512
    | exact resolve eq14512 eq1589
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1589 eq14512
  have eq14612 : (M.op x y) = (k x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq14611
  have eq14760 : ∀ X0 : G, x = (M.op (M.op x y) (M.op (k X0 X0) x)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1579 x X0
       have i₂ := eq14612
       grind)
    | exact superpose eq14612 eq1579
    | exact resolve eq1579 eq14612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1579 eq14612
  have eq14886 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1588 eq14760
    | exact resolve eq14760 eq1588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1588 eq14760
  have eq14887 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq14886
  have eq14986 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq14887 eq31
    | exact resolve eq31 eq14887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq14887
  have eq15016 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq14986
    | exact resolve eq14986 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq14986
  have eq15017 : x = y := by grind
  clear eq15016
  have eq15019 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq15017
       grind)
    | exact superpose eq15017 eq18
    | exact resolve eq18 eq15017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq15020 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq15017
       grind)
    | exact superpose eq15017 eq24
    | exact resolve eq24 eq15017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq15017
  have eq15037 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq15020
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15020
    | exact resolve eq15020 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15020
  have eq15038 : (M.op x y) = (k x x) := by
    first
    | (have i₁ := eq15019
       have i₂ := eq174 x
       grind)
    | exact superpose eq174 eq15019
    | exact resolve eq15019 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15019
  have eq15039 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq15037 eq26
    | exact resolve eq26 eq15037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq15037
  have eq15070 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq15039
       have i₂ := eq174 sF2
       grind)
    | exact superpose eq174 eq15039
    | exact resolve eq15039 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq15039
  have eq15075 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq15038
       grind)
    | exact superpose eq15038 eq39
    | exact resolve eq39 eq15038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq15038
  have eq15375 : (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq15075
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq15075
    | exact resolve eq15075 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq15075
  have eq15464 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq15070 eq15375
    | exact resolve eq15375 eq15070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15070 eq15375
  have eq15508 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq15464
    | exact resolve eq15464 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq15464
  have eq15527 : False := by grind
  exact eq15527

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_pxy_pyx_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq14 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq84 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq91 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq84
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq84
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq84 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq91
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq91
    | exact resolve eq91 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq97
    | exact resolve eq97 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq480 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq54 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq482 : ∀ X0 X1 X2 : G, (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) X0 X1
       have i₂ := eq14 (M.op (M.op X0 (M.op X1 X1)) (M.op X2 X2)) (M.op X0 (M.op X1 X1)) X2
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op (M.op X3 X3) (M.op X4 X4)) (M.op (M.op X1 (M.op X2 X2)) X0))) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 (M.op (M.op X1 (M.op X2 X2)) X0) X3 X4 X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq554 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X1) = (M.op X0 (M.op (M.op (M.op X4 X4) (M.op X5 X5)) (M.op X1 X0))) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq53 (M.op X1 X0) X4 X5 (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X1)
       have i₂ := eq53 X1 X2 X3 X0
       grind)
    | exact superpose eq53 eq53
    | exact resolve eq53 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : ∀ X0 X1 : G, y = (M.op (M.op x y) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) x)) := by
    intro X0 X1
    first
    | (have i₁ := eq53 x X0 X1 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq53
    | (have j0 := eq53 x X0 X1 y
       grind)
    | exact resolve eq53 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq557 : ∀ X0 X1 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq27 eq53
    | (have j0 := eq53 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq53 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq560 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X2) (M.op (M.op (σ (M.op X0 X0)) (M.op X3 X3)) X1)) = X2 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq53 X1 (σ X0) X3 X2
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq53
    | exact resolve eq53 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq564 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 x (M.op X0 X0) X2
       have i₂ := eq54 x (M.op X0 X0) X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq578 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1))) X3) X2) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X2 (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op X0 X0) (M.op X1 X1)))
       have i₂ := eq53 (M.op (M.op X0 X0) (M.op X1 X1)) X0 X1 (M.op (M.op X0 X0) (M.op X1 X1))
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq830 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op (M.op X3 X3) (M.op X4 X4)) X2)) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq53 X2 X3 X4 X2
       have i₂ := eq480 X1 X0 X2
       grind)
    | (have i₁ := eq53 (M.op X1 X1) X1 X2 (M.op X0 X0)
       have i₂ := eq480 X0 X1 X2
       grind)
    | exact superpose eq480 eq53
    | exact resolve eq53 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq942 : ∀ X0 X1 X2 X4 : G, (M.op (M.op X2 (M.op (M.op X0 X0) (M.op X1 X1))) (M.op X4 X4)) = X2 := by
    intro X0 X1 X2 X4
    first
    | (have i₁ := eq482 X2 x X4
       have i₂ := eq480 X1 X0 x
       grind)
    | (have i₁ := eq482 X0 (M.op X0 X0) X2
       have i₂ := eq480 X0 X0 X2
       grind)
    | exact superpose eq480 eq482
    | exact resolve eq482 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5932 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op (M.op X4 X4) (M.op (M.op X1 (M.op (M.op X2 X2) (M.op X3 X3))) X0))) = X1 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq564 X4 (M.op (M.op X1 (M.op (M.op X2 X2) (M.op X3 X3))) X0) X1
       have i₂ := eq578 X2 X3 X1 X0
       grind)
    | exact superpose eq578 eq564
    | exact resolve eq564 eq578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq578
  have eq5993 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op (σ (M.op X3 X3)) (M.op X4 X4)) X2)) = X2 := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq560 X3 X2 X2 X4
       have i₂ := eq480 X1 X0 X2
       grind)
    | (have i₁ := eq560 X0 (M.op X1 X1) (M.op X0 X0) X3
       have i₂ := eq480 X0 X1 X2
       grind)
    | exact superpose eq480 eq560
    | exact resolve eq560 eq480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq480
  have eq6024 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) x) = (M.op y (M.op (M.op (σ (M.op X2 X2)) (M.op X3 X3)) (M.op x y))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq556 eq560
    | exact resolve eq560 eq556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq6032 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (σ x)) = (M.op (σ y) (M.op (M.op (σ (M.op X2 X2)) (M.op X3 X3)) (M.op (σ x) (σ y)))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq557 eq560
    | exact resolve eq560 eq557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq557 eq560
  have eq7192 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X1 X1) (M.op (M.op (M.op X2 X2) (M.op X3 X3)) X0)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq552 (M.op X1 X1) X0 x X2 X3
       have i₂ := eq482 X0 x X1
       grind)
    | exact superpose eq482 eq552
    | exact resolve eq552 eq482
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq7262 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op (M.op X0 (M.op X4 X4)) X1)) = (M.op X0 (M.op (M.op X5 X5) X1)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq564 X5 X1 (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op (M.op X0 (M.op X4 X4)) X1))
       have i₂ := eq552 X1 X0 X4 X2 X3
       grind)
    | exact superpose eq552 eq564
    | exact resolve eq564 eq552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq9788 : ∀ X0 X1 X2 X3 X4 X5 X6 : G, (M.op (M.op (M.op X1 X1) (M.op X2 X2)) (M.op X3 X0)) = (M.op (M.op (M.op X4 X4) X3) (M.op (M.op (M.op X5 X5) (M.op X6 X6)) X0)) := by
    intro X0 X1 X2 X3 X4 X5 X6
    first
    | (have i₁ := eq554 (M.op (M.op X4 X4) X3) (M.op X3 X0) X1 X2 X5 X6
       have i₂ := eq564 X4 X3 X0
       grind)
    | exact superpose eq564 eq554
    | exact resolve eq554 eq564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq564
  have eq28408 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq99 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq28409 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq28408
    | exact resolve eq28408 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28408
  have eq28414 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq28409
       have r₂ := eq28
       grind)
    | exact resolve eq28409 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28409
  have eq28416 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq28414
    | exact resolve eq28414 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28414
  have eq492423 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 : G, (M.op (M.op (M.op X7 X7) X6) (M.op (M.op X8 X8) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (M.op (M.op (M.op X2 (M.op (M.op X3 X3) (M.op X4 X4))) (M.op X5 X5)) X6)))) = X2 := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8
    first
    | (have i₁ := eq5932 (M.op (M.op X7 X7) X6) X2 X3 X4 X8
       have i₂ := eq7262 (M.op X2 (M.op (M.op X3 X3) (M.op X4 X4))) X6 X0 X1 X5 X7
       grind)
    | (have i₁ := eq5932 (M.op (M.op X0 (M.op X4 X4)) X1) (M.op X2 X2) X2 X2 X4
       have i₂ := eq7262 X0 X1 X2 (M.op X2 X2) X4 X5
       grind)
    | exact superpose eq7262 eq5932
    | exact resolve eq5932 eq7262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5932 eq7262
  have eq492610 : ∀ X2 X3 X4 X5 X6 X7 : G, (M.op (M.op (M.op X7 X7) X6) (M.op (M.op (M.op X2 (M.op (M.op X3 X3) (M.op X4 X4))) (M.op X5 X5)) X6)) = X2 := by
    intro X2 X3 X4 X5 X6 X7
    first
    | (have i₁ := eq492423 x x X2 X3 X4 X5 X6 X7 x
       have i₂ := eq7192 (M.op (M.op (M.op X2 (M.op (M.op X3 X3) (M.op X4 X4))) (M.op X5 X5)) X6) x x x
       grind)
    | exact superpose eq7192 eq492423
    | exact resolve eq492423 eq7192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7192 eq492423
  have eq495852 : ∀ X2 X6 X7 : G, (M.op (M.op (M.op X7 X7) X6) (M.op X2 X6)) = X2 := by
    intro X2 X6 X7
    first
    | (have i₁ := eq492610 X2 x x x X6 X7
       have i₂ := eq942 x x X2 x
       grind)
    | exact superpose eq942 eq492610
    | exact resolve eq492610 eq942
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942 eq492610
  have eq809725 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) x)) = (M.op (M.op (M.op X6 X6) y) (M.op (M.op (M.op X7 X7) (M.op X8 X8)) (M.op (M.op (σ (M.op X4 X4)) (M.op X5 X5)) (M.op x y)))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8
    first
    | exact superpose eq6024 eq9788
    | exact resolve eq9788 eq6024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6024
  have eq809808 : ∀ X0 X1 X2 X3 X4 X5 X6 X7 X8 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (σ x))) = (M.op (M.op (M.op X6 X6) (σ y)) (M.op (M.op (M.op X7 X7) (M.op X8 X8)) (M.op (M.op (σ (M.op X4 X4)) (M.op X5 X5)) (M.op (σ x) (σ y))))) := by
    intro X0 X1 X2 X3 X4 X5 X6 X7 X8
    first
    | exact superpose eq6032 eq9788
    | exact resolve eq9788 eq6032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6032 eq9788
  have eq817750 : ∀ X0 X1 X2 X3 X6 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) (σ x))) = (M.op (M.op (M.op X6 X6) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2 X3 X6
    first
    | (have i₁ := eq809808 X0 X1 X2 X3 X3 x X6 X0 X1
       have i₂ := eq5993 X0 X1 sF4 X3 x
       grind)
    | exact superpose eq5993 eq809808
    | exact resolve eq809808 eq5993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809808
  have eq817760 : ∀ X0 X1 X2 X3 X6 : G, (M.op (M.op (M.op X2 X2) (M.op X3 X3)) (M.op (M.op (M.op X0 X0) (M.op X1 X1)) x)) = (M.op (M.op (M.op X6 X6) y) (M.op x y)) := by
    intro X0 X1 X2 X3 X6
    first
    | (have i₁ := eq809725 X0 X1 X2 X3 X3 x X6 X0 X1
       have i₂ := eq5993 X0 X1 sF0 X3 x
       grind)
    | exact superpose eq5993 eq809725
    | exact resolve eq809725 eq5993
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5993 eq809725
  have eq818928 : ∀ X6 : G, (σ x) = (M.op (M.op (M.op X6 X6) (σ y)) (M.op (σ x) (σ y))) := by
    intro X6
    first
    | (have i₁ := eq817750 x x x x X6
       have i₂ := eq830 x x sF2 x x
       grind)
    | exact superpose eq830 eq817750
    | exact resolve eq817750 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq817750
  have eq818932 : ∀ X6 : G, x = (M.op (M.op (M.op X6 X6) y) (M.op x y)) := by
    intro X6
    first
    | (have i₁ := eq817760 x x x x X6
       have i₂ := eq830 x x x x x
       grind)
    | exact superpose eq830 eq817760
    | exact resolve eq817760 eq830
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq830 eq817760
  have eq2750423 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op X0 X0) (σ y)) (M.op (σ x) (σ y))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq28416 eq495852
    | exact resolve eq495852 eq28416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28416
  have eq2753380 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq818928 eq2750423
    | exact resolve eq2750423 eq818928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818928 eq2750423
  have eq2753381 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq2753380
  have eq2755628 : ∀ X0 : G, y = (M.op (M.op (M.op X0 X0) y) (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq495852 y y X0
       have i₂ := eq2753381
       grind)
    | exact superpose eq2753381 eq495852
    | exact resolve eq495852 eq2753381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495852 eq2753381
  have eq2755882 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq818932 eq2755628
    | exact resolve eq2755628 eq818932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq818932 eq2755628
  have eq2755883 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq2755882
  have eq2756365 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2755883 eq30
    | exact resolve eq30 eq2755883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2755883
  have eq2756523 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq2756365
    | exact resolve eq2756365 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2756365
  have eq2756524 : x = y := by grind
  clear eq2756523
  have eq2756555 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq2756524
       grind)
    | exact superpose eq2756524 eq19
    | exact resolve eq19 eq2756524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2756556 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq2756524
       grind)
    | exact superpose eq2756524 eq25
    | exact resolve eq25 eq2756524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2756524
  have eq2756941 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2756556
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2756556
    | exact resolve eq2756556 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2756556
  have eq2756970 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2756941 eq27
    | exact resolve eq27 eq2756941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2756941
  have eq2759670 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2756970 eq66
    | exact resolve eq66 eq2756970
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq2756970
  have eq2761372 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2759670
       have i₂ := eq2756555
       grind)
    | exact superpose eq2756555 eq2759670
    | exact resolve eq2759670 eq2756555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2756555 eq2759670
  have eq2761828 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2761372 eq15
    | exact resolve eq15 eq2761372
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2761372
  have eq2762707 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq2761828
    | exact resolve eq2761828 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2761828
  have eq2762885 : False := by grind
  exact eq2762885

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pxx_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq14 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq488 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq54 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq846 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) ≠ (M.op (M.op X0 X0) (M.op X1 X1)) ∨ X2 = X3 ∨ (M.op X2 X3) = (k X2 X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 X3
       have i₂ := eq488 X1 X0 X3
       grind)
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq488 X0 X0 X2
       grind)
    | exact superpose eq488 eq12
    | (have j0 := eq12 X2 X3
       grind)
    | (have r₁ := eq12 X2 (M.op X0 X0)
       have r₂ := eq488 X0 X0 X2
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X2
       have r₂ := eq488 X0 X0 X2
       grind)
    | exact resolve eq12 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq889 : ∀ X2 X3 : G, (M.op X2 X3) = (k X2 X3) ∨ X2 = X3 := by
    intro X2 X3
    first
    | (have j0 := eq846 x x X2 X3
       grind)
    | (have r₁ := eq846 x x X2 X3
       have r₂ := eq488 x x X2
       grind)
    | (have r₁ := eq846 x x (M.op x x) X3
       have r₂ := eq488 x x (M.op x x)
       grind)
    | exact resolve eq846 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488 eq846
  have eq2603 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq889 x y
       grind)
    | exact superpose eq889 eq49
    | (have j1 := eq889 (σ (M.op x y)) (k (σ x) (σ y))
       grind)
    | exact resolve eq49 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq2629 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq2603
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2603
    | exact resolve eq2603 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2603
  have eq2630 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq2629
    | exact resolve eq2629 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2629
  have eq2634 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2630 eq889
    | (have j0 := eq889 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq889 eq2630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889 eq2630
  have eq2639 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq2634
    | exact resolve eq2634 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2634
  have eq2642 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2639
       have r₂ := eq28
       grind)
    | exact resolve eq2639 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2639
  have eq2645 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2642 eq30
    | exact resolve eq30 eq2642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2642
  have eq2662 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq2645
    | exact resolve eq2645 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2645
  have eq2663 : x = y := by grind
  clear eq2662
  have eq2821 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq2663
       grind)
    | exact superpose eq2663 eq19
    | exact resolve eq19 eq2663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2822 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq2663
       grind)
    | exact superpose eq2663 eq25
    | exact resolve eq25 eq2663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2663
  have eq2838 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2822
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2822
    | exact resolve eq2822 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2822
  have eq2841 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2838 eq27
    | exact resolve eq27 eq2838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2838
  have eq2919 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2841 eq66
    | exact resolve eq66 eq2841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq2841
  have eq2963 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2919
       have i₂ := eq2821
       grind)
    | exact superpose eq2821 eq2919
    | exact resolve eq2919 eq2821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2821 eq2919
  have eq2964 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2963 eq15
    | exact resolve eq15 eq2963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2963
  have eq2989 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq2964
    | exact resolve eq2964 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2964
  have eq2994 : False := by grind
  exact eq2994

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pyx_pxx_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq14 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  clear eq37
  have eq488 : ∀ X0 X1 X2 : G, (M.op X2 X2) = (M.op (M.op X1 X1) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq54 X1 (M.op X2 X2) (M.op X0 X0)
       have i₂ := eq54 X2 (M.op X0 X0) X0
       grind)
    | exact superpose eq54 eq54
    | exact resolve eq54 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq846 : ∀ X0 X1 X2 X3 : G, (M.op X2 X2) ≠ (M.op (M.op X0 X0) (M.op X1 X1)) ∨ X2 = X3 ∨ (k X2 X3) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq12 X2 X3
       have i₂ := eq488 X1 X0 X3
       grind)
    | (have i₁ := eq12 X0 (M.op X0 X0)
       have i₂ := eq488 X0 X0 X2
       grind)
    | exact superpose eq488 eq12
    | (have j0 := eq12 X2 X3
       grind)
    | (have r₁ := eq12 X2 (M.op X0 X0)
       have r₂ := eq488 X0 X0 X2
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X2
       have r₂ := eq488 X0 X0 X2
       grind)
    | exact resolve eq12 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq889 : ∀ X2 X3 : G, (k X2 X3) = (M.op X3 X2) ∨ X2 = X3 := by
    intro X2 X3
    first
    | (have j0 := eq846 x x X2 X3
       grind)
    | (have r₁ := eq846 x x X2 X3
       have r₂ := eq488 x x X2
       grind)
    | (have r₁ := eq846 x x (M.op x x) X3
       have r₂ := eq488 x x (M.op x x)
       grind)
    | exact resolve eq846 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488 eq846
  have eq2607 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq92
       have i₂ := eq889 y x
       grind)
    | exact superpose eq889 eq92
    | (have j1 := eq889 (σ (M.op x y)) (k (σ y) (σ x))
       grind)
    | exact resolve eq92 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq2629 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq2607
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq2607
    | exact resolve eq2607 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2607
  have eq2630 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y := by
    first
    | exact superpose eq21 eq2629
    | exact resolve eq2629 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2629
  have eq2634 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq2630 eq889
    | (have j0 := eq889 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq889 eq2630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889 eq2630
  have eq2639 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq2634
    | exact resolve eq2634 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2634
  have eq2642 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq2639
       have r₂ := eq28
       grind)
    | exact resolve eq2639 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2639
  have eq2645 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq2642 eq30
    | exact resolve eq30 eq2642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq2642
  have eq2662 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq2645
    | exact resolve eq2645 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2645
  have eq2663 : x = y := by grind
  clear eq2662
  have eq2821 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq2663
       grind)
    | exact superpose eq2663 eq19
    | exact resolve eq19 eq2663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2822 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq2663
       grind)
    | exact superpose eq2663 eq25
    | exact resolve eq25 eq2663
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2663
  have eq2838 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq2822
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq2822
    | exact resolve eq2822 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2822
  have eq2841 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2838 eq27
    | exact resolve eq27 eq2838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq2838
  have eq2919 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq2841 eq66
    | exact resolve eq66 eq2841
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq2841
  have eq2963 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq2919
       have i₂ := eq2821
       grind)
    | exact superpose eq2821 eq2919
    | exact resolve eq2919 eq2821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2821 eq2919
  have eq2964 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2963 eq15
    | exact resolve eq15 eq2963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2963
  have eq2989 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq2964
    | exact resolve eq2964 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq2964
  have eq2994 : False := by grind
  exact eq2994

/-- `Equation3008`: `x = ((y ◇ (z ◇ z)) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_pyy_pxx_pxy_pyx_Equation3008 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3008 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3008.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (M.op X2 X2)) X0) X1) = X0 := by
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
  have eq53 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X3) (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op (M.op (M.op X1 X1) (M.op X2 X2)) X0) X1
       have i₂ := eq14 X0 (M.op X1 X1) X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X1 (M.op X2 X2))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 (M.op X1 (M.op X2 X2)) X0
       have i₂ := eq14 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq85 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq85
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq85
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq99 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq21 eq98
    | exact resolve eq98 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
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
  have eq410 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 (σ (M.op X0 X0))) X2) X1) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 X1 (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq566 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (M.op X0 X0) X1)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq53 X1 x (M.op X0 X0) X2
       have i₂ := eq54 x (M.op X0 X0) X0
       grind)
    | exact superpose eq54 eq53
    | exact resolve eq53 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq54
  have eq1369 : ∀ X0 : G, y = (M.op (M.op x y) (M.op (M.op X0 X0) x)) := by
    intro X0
    first
    | (have i₁ := eq566 X0 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq566
    | (have j0 := eq566 X0 x y
       grind)
    | exact resolve eq566 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1370 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (M.op X0 X0) (σ x))) := by
    intro X0
    first
    | exact superpose eq27 eq566
    | (have j0 := eq566 X0 (σ x) (σ y)
       grind)
    | exact resolve eq566 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1685 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op X0 (σ (M.op X1 X1)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq566 (M.op X0 (σ (M.op X1 X1))) X0 X2
       have i₂ := eq410 X1 X0 (M.op X0 (σ (M.op X1 X1)))
       grind)
    | exact superpose eq410 eq566
    | exact resolve eq566 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq1693 : ∀ X0 : G, y = (M.op (M.op x y) (M.op x (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1369 (M.op x (σ (M.op X0 X0)))
       have i₂ := eq410 X0 x (M.op x (σ (M.op X0 X0)))
       grind)
    | exact superpose eq410 eq1369
    | exact resolve eq1369 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq1694 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ (M.op X0 X0)))) := by
    intro X0
    first
    | (have i₁ := eq1370 (M.op sF2 (σ (M.op X0 X0)))
       have i₂ := eq410 X0 sF2 (M.op sF2 (σ (M.op X0 X0)))
       grind)
    | exact superpose eq410 eq1370
    | exact resolve eq1370 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq1370
  have eq27666 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq100 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq27667 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq27666
    | exact resolve eq27666 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27666
  have eq27672 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | (have r₁ := eq27667
       have r₂ := eq28
       grind)
    | exact resolve eq27667 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27667
  have eq27674 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq27 eq27672
    | exact resolve eq27672 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27672
  have eq27827 : ∀ X0 : G, (σ x) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ (M.op X0 X0)))) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27674 eq1685
    | exact resolve eq1685 eq27674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27674
  have eq27830 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op x x) ∨ x = y := by
    first
    | exact superpose eq1694 eq27827
    | exact resolve eq27827 eq1694
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694 eq27827
  have eq27831 : (M.op x y) = (M.op x x) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq27830
  have eq27995 : ∀ X0 : G, x = (M.op (M.op x y) (M.op x (σ (M.op X0 X0)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1685 x X0 x
       have i₂ := eq27831
       grind)
    | exact superpose eq27831 eq1685
    | exact resolve eq1685 eq27831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1685 eq27831
  have eq27998 : x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq1693 eq27995
    | exact resolve eq27995 eq1693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1693 eq27995
  have eq27999 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq27998
  have eq28056 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq27999 eq30
    | exact resolve eq30 eq27999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq27999
  have eq28084 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq28056
    | exact resolve eq28056 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq28056
  have eq28085 : x = y := by grind
  clear eq28084
  have eq28238 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq28085
       grind)
    | exact superpose eq28085 eq19
    | exact resolve eq19 eq28085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq28239 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq28085
       grind)
    | exact superpose eq28085 eq25
    | exact resolve eq25 eq28085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq28085
  have eq28339 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq28239
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq28239
    | exact resolve eq28239 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq28239
  have eq28354 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq28339 eq27
    | exact resolve eq27 eq28339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq28339
  have eq28643 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq28354 eq66
    | exact resolve eq66 eq28354
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq28354
  have eq28822 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq28643
       have i₂ := eq28238
       grind)
    | exact superpose eq28238 eq28643
    | exact resolve eq28643 eq28238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28238 eq28643
  have eq28825 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq28822 eq15
    | exact resolve eq15 eq28822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28822
  have eq28870 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq28825
    | exact resolve eq28825 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq28825
  have eq28879 : False := by grind
  exact eq28879
