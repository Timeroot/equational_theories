import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_x_y_pyx_pxx_pyx_Equation1483 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
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
  have eq100 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq112 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq114 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 ∨ (M.op (τ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq502 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq100 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq100
    | exact resolve eq100 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq521 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq502 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq502
    | (have j0 := eq502 X0
       grind)
    | exact resolve eq502 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq502
  have eq524 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq521 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq521
    | (have j0 := eq521 X0
       grind)
    | exact resolve eq521 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq521
  have eq525 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq524 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq524 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq524 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq524
  have eq536 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq525 (σ X0)
       grind)
    | exact superpose eq525 eq15
    | exact resolve eq15 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq555 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq536 X0
       have i₂ := eq525 X0
       grind)
    | exact superpose eq525 eq536
    | exact resolve eq536 eq525
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525 eq536
  have eq2891 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq112 x y
       grind)
    | exact superpose eq112 eq16
    | (have j1 := eq112 x y
       grind)
    | exact resolve eq16 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112
  have eq4118 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq114 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq114
    | exact resolve eq114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq4195 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4118 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4118
    | (have j0 := eq4118 X0 X1
       grind)
    | exact resolve eq4118 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4118
  have eq11091 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2891
       have i₂ := eq4195 y x
       grind)
    | exact superpose eq4195 eq2891
    | (have j1 := eq4195 (σ x) (σ y)
       grind)
    | (have r₁ := eq2891
       have r₂ := eq4195 y x
       grind)
    | (have r₁ := eq2891
       have r₂ := eq4195 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq2891
       have r₂ := eq4195 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq2891 eq4195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11092 : x = y ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq11091
  have eq11442 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11092
       grind)
    | exact superpose eq11092 eq16
    | exact resolve eq16 eq11092
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11092
  have eq11443 : x = (M.op y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq11442
       have r₂ := eq555 x
       grind)
    | exact resolve eq11442 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11442
  have eq11446 : x ≠ x ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq11443
       grind)
    | exact superpose eq11443 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11443
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq11443
       grind)
    | exact resolve eq12 eq11443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11443
  have eq11474 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq11446
  have eq11552 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2891
       have i₂ := eq11474
       grind)
    | exact superpose eq11474 eq2891
    | exact resolve eq2891 eq11474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2891 eq11474
  have eq11553 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq11552
  have eq11554 : (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq11553
  have eq11569 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq11554
       grind)
    | exact superpose eq11554 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq11554
       grind)
    | exact resolve eq12 eq11554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11554
  have eq11597 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq11569
  have eq11607 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11597
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq11597
    | exact resolve eq11597 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11597
  have eq11683 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11607
       grind)
    | exact superpose eq11607 eq16
    | exact resolve eq16 eq11607
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11607
  have eq11730 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq11683
       have i₂ := eq4195 y x
       grind)
    | exact superpose eq4195 eq11683
    | (have j1 := eq4195 (σ x) (σ y)
       grind)
    | (have r₁ := eq11683
       have r₂ := eq4195 y x
       grind)
    | (have r₁ := eq11683
       have r₂ := eq4195 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq11683
       have r₂ := eq4195 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq11683 eq4195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4195
  have eq11731 : x = y ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by grind
  clear eq11730
  have eq11735 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11731
       grind)
    | exact superpose eq11731 eq16
    | exact resolve eq16 eq11731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11731
  have eq11736 : x = (M.op y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq11735
       have r₂ := eq555 x
       grind)
    | exact resolve eq11735 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11735
  have eq11739 : x ≠ x ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq11736
       grind)
    | exact superpose eq11736 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq11736
       grind)
    | exact resolve eq12 eq11736
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11736
  have eq11767 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq11739
  have eq11845 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq11683
       have i₂ := eq11767
       grind)
    | exact superpose eq11767 eq11683
    | exact resolve eq11683 eq11767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11683 eq11767
  have eq11849 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq11845
  have eq11850 : (σ x) = (σ y) := by grind
  clear eq11849
  have eq11851 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11850
       grind)
    | exact superpose eq11850 eq16
    | exact resolve eq16 eq11850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11852 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq11850
       grind)
    | exact superpose eq11850 eq10
    | exact resolve eq10 eq11850
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11850
  have eq11929 : x = y := by
    first
    | (have i₁ := eq11852
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11852
    | exact resolve eq11852 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11852
  have eq11930 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq11851
       have i₂ := eq555 x
       grind)
    | exact superpose eq555 eq11851
    | exact resolve eq11851 eq555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555 eq11851
  have eq11933 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq11930
       have i₂ := eq11929
       grind)
    | exact superpose eq11929 eq11930
    | exact resolve eq11930 eq11929
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11929 eq11930
  have eq11934 : False := by grind
  exact eq11934

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_pyy_pxy_pyy_pxy_Equation1483 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
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
  have eq23 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq23 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq23 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq23 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq28 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X0 := by
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
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
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
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq33 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq28 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq34 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq34 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq34 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq39 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq39 (k X0 X0) X0
       have r₂ := eq12 X0 (k X0 X0)
       grind)
    | (have r₁ := eq39 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq39 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq52 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq41 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq41 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq41 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq46
    | (have j0 := eq46 X0 X1
       grind)
    | exact resolve eq46 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq55 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X0 X1
       have i₂ := eq24 X1
       grind)
    | exact superpose eq24 eq47
    | (have j0 := eq47 X0 X1
       grind)
    | exact resolve eq47 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq47
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       have j1 := eq54 X0 X1
       grind)
    | (have r₁ := eq55 X0 X1
       have r₂ := eq54 X0 X1
       grind)
    | exact resolve eq55 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq55
  have eq138 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq52 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq142 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq138 X0 X1
       have j1 := eq57 X0 X1
       grind)
    | (have r₁ := eq138 X0 X1
       have r₂ := eq57 X0 X1
       grind)
    | (have r₁ := eq138 X0 X0
       have r₂ := eq57 X0 X0
       grind)
    | exact resolve eq138 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq138
  have eq290 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq142 (σ X0) (σ X1)
       grind)
    | exact superpose eq142 eq15
    | exact resolve eq15 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq290 X0 X1
       have i₂ := eq142 X0 X1
       grind)
    | exact superpose eq142 eq290
    | exact resolve eq290 eq142
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq290
  have eq299 : False := by grind
  exact eq299

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_x_pxy_Equation1483 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = a :=
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
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X2))) = X0 := by
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
  clear eq24 eq35
  have eq51 : ∀ X0 : G, (σ y) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) (M.op (σ x) X0))) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ y) (σ x) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : x ≠ (M.op x y) ∨ y = (M.op y x) ∨ x = (k x y) := by
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
  have eq79 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq96 x y
       grind)
    | exact superpose eq96 eq44
    | (have j1 := eq96 x y
       grind)
    | exact resolve eq44 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq108
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq108
    | exact resolve eq108 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq121 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq119
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq122 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq121
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq121
    | exact resolve eq121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq122 eq96
    | (have j0 := eq96 (σ x) (σ y)
       grind)
    | exact resolve eq96 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq126
       have r₂ := eq27
       grind)
    | exact resolve eq126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq131 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq129
    | exact resolve eq129 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq133 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131 eq27
    | exact resolve eq27 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq237 : ∀ X0 : G, (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) X0))) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq131 eq51
    | exact resolve eq51 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq244 : (σ y) = (M.op (σ x) (M.op (σ y) (M.op (σ x) (σ y)))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq237
    | (have j0 := eq237 (σ y)
       grind)
    | exact resolve eq237 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq253 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131 eq244
    | exact resolve eq244 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq244
  have eq262 : (σ y) = (M.op (σ x) (M.op (σ y) (σ x))) ∨ x = (M.op x y) := by grind
  clear eq253
  have eq601 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq131 eq79
    | (have r₁ := eq79
       have r₂ := eq131
       grind)
    | exact resolve eq79 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq602 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq601
  have eq605 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq602 eq262
    | exact resolve eq262 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq602
  have eq619 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (k (σ x) (σ y)) := by grind
  clear eq605
  have eq626 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq619
    | exact resolve eq619 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq630 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq626 eq122
    | exact resolve eq122 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq634 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq630
  have eq639 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq634
       have r₂ := eq133
       grind)
    | exact resolve eq634 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq634
  have eq648 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq639 eq131
    | exact resolve eq131 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq667 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq648
  have eq713 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq667 eq26
    | exact resolve eq26 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq722 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq667 eq122
    | exact resolve eq122 eq667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq667
  have eq756 : (σ (M.op x y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq722
  have eq950 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq713 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq713
       grind)
    | exact resolve eq13 eq713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq713
  have eq965 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq950
       have r₂ := eq131
       grind)
    | exact resolve eq950 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq950
  have eq1133 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq965 eq756
    | exact resolve eq756 eq965
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq756 eq965
  have eq1136 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq1133
  have eq1138 : x = (M.op x y) := by
    first
    | (have r₁ := eq1136
       have r₂ := eq27
       grind)
    | exact resolve eq1136 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1136
  have eq1140 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1138 eq20
    | exact resolve eq20 eq1138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1146 : x ≠ x ∨ y = (M.op y x) ∨ x = (k x y) := by
    first
    | exact superpose eq1138 eq78
    | (have r₁ := eq78
       have r₂ := eq1138
       grind)
    | exact resolve eq78 eq1138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq1152 : y = (M.op y x) ∨ x = (k x y) := by grind
  clear eq1146
  have eq1159 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1140
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1140
    | exact resolve eq1140 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140
  have eq1177 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1159 eq26
    | exact resolve eq26 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1977 : y ≠ y ∨ (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq1152
       grind)
    | exact superpose eq1152 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1152
       grind)
    | exact resolve eq13 eq1152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1152
  have eq1988 : (M.op x y) = (k x y) ∨ x = (k x y) := by grind
  clear eq1977
  have eq1991 : (M.op x y) = (k x y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq1988
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1988
    | exact resolve eq1988 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1988
  have eq1997 : x = (k x y) ∨ x = (k x y) := by
    first
    | exact superpose eq1138 eq1991
    | exact resolve eq1991 eq1138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1138 eq1991
  have eq1998 : x = (k x y) := by grind
  clear eq1997
  have eq2006 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1998
       grind)
    | exact superpose eq1998 eq44
    | exact resolve eq44 eq1998
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1998
  have eq2013 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1159 eq2006
    | exact resolve eq2006 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2006
  have eq2015 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq2013
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2013
    | exact resolve eq2013 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2013
  have eq2016 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq1159 eq2015
    | exact resolve eq2015 eq1159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1159 eq2015
  have eq2020 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq2016 eq96
    | (have j0 := eq96 (σ (M.op x y)) (σ y)
       grind)
    | exact resolve eq96 eq2016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq2016
  have eq2021 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ y)) := by grind
  clear eq2020
  have eq2023 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1177 eq2021
    | exact resolve eq2021 eq1177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1177 eq2021
  have eq2026 : False := by grind
  exact eq2026

/-- `Equation1483`: `x = (y ◇ x) ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_x_pxy_x_pxy_Equation1483 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law1483 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1483.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq62 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X0) X2) (M.op X2 X0)) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X2 (M.op X1 X0) (M.op X0 (M.op X1 x))
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq356 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq357 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq356 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq356
  have eq359 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq357 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq357 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq357 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq370 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq359 (σ X0)
       grind)
    | exact superpose eq359 eq15
    | exact resolve eq15 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq389 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq370 X0
       have i₂ := eq359 X0
       grind)
    | exact superpose eq359 eq370
    | exact resolve eq370 eq359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq359 eq370
  have eq436 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (M.op X1 (σ X0)) (σ X0)) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq62 (σ X0) X1 (σ X0)
       have i₂ := eq389 X0
       grind)
    | exact superpose eq389 eq62
    | exact resolve eq62 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq441 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (M.op X1 (σ X0)) = X1 ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0)
       have i₂ := eq389 X0
       grind)
    | exact superpose eq389 eq14
    | (have j0 := eq14 X1 (σ X0)
       grind)
    | exact resolve eq14 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq442 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq389 X0
       grind)
    | exact superpose eq389 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq443 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op X1 (σ X0)) ∨ (M.op X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq441 X0 X1
       have j1 := eq442 X0 X1
       grind)
    | (have r₁ := eq441 X0 X1
       have r₂ := eq442 X0 X1
       grind)
    | exact resolve eq441 eq442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq441 eq442
  have eq794 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq443 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq443
    | exact resolve eq443 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq805 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq443 X1 (σ X0)
       grind)
    | exact superpose eq443 eq15
    | (have j1 := eq443 X1 (σ X0)
       grind)
    | exact resolve eq15 eq443
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq834 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq794 (τ X1) X0
       grind)
    | exact superpose eq794 eq18
    | (have j1 := eq794 (τ X1) X0
       grind)
    | exact resolve eq18 eq794
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq794
  have eq1436 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq834 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq834
    | exact resolve eq834 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834
  have eq1513 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1436 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1436
    | (have j0 := eq1436 X0 X1
       grind)
    | exact resolve eq1436 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1436
  have eq2328 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq805 x y
       grind)
    | exact superpose eq805 eq16
    | (have j1 := eq805 x y
       grind)
    | exact resolve eq16 eq805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2393 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq805 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq805
  have eq2573 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2328
       have i₂ := eq1513 y x
       grind)
    | exact superpose eq1513 eq2328
    | (have j1 := eq1513 (σ y) (σ x)
       grind)
    | (have r₁ := eq2328
       have r₂ := eq1513 y x
       grind)
    | exact resolve eq2328 eq1513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2574 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2573
  have eq2579 : x ≠ x ∨ y = (M.op y y) ∨ x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq2574
       grind)
    | exact superpose eq2574 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq2574
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq2574
       grind)
    | exact resolve eq13 eq2574
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2574
  have eq2592 : x = (k x y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2579
  have eq4005 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2393 x y
       have i₂ := eq2592
       grind)
    | exact superpose eq2592 eq2393
    | (have j0 := eq2393 x y
       grind)
    | exact resolve eq2393 eq2592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2393 eq2592
  have eq4014 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq4005
  have eq4015 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq4014
  have eq4023 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4015
       grind)
    | exact superpose eq4015 eq16
    | exact resolve eq16 eq4015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4030 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq4015
       grind)
    | exact superpose eq4015 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq4015
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq4015
       grind)
    | exact resolve eq13 eq4015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4015
  have eq4043 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq4030
  have eq4046 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq4043
       have i₂ := eq389 y
       grind)
    | exact superpose eq389 eq4043
    | exact resolve eq4043 eq389
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4043
  have eq4049 : (σ x) = (σ (k x y)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq4046
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq4046
    | exact resolve eq4046 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4046
  have eq7797 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1513 y x
       have i₂ := eq4049
       grind)
    | exact superpose eq4049 eq1513
    | (have j0 := eq1513 y x
       grind)
    | exact resolve eq1513 eq4049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1513 eq4049
  have eq7866 : x = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq7797
       have r₂ := eq4023
       grind)
    | exact resolve eq7797 eq4023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7797
  have eq7907 : (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq4023
       have i₂ := eq7866
       grind)
    | exact superpose eq7866 eq4023
    | exact resolve eq4023 eq7866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4023 eq7866
  have eq7940 : (σ x) ≠ (σ x) ∨ y = (M.op y y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq7907
  have eq7941 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by grind
  clear eq7940
  have eq7966 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq7941
       grind)
    | exact superpose eq7941 eq10
    | exact resolve eq10 eq7941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7941
  have eq8036 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq7966
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq7966
    | exact resolve eq7966 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7966
  have eq8037 : y = (M.op y y) := by grind
  clear eq8036
  have eq8177 : ∀ X0 : G, y ≠ y ∨ (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq8037
       grind)
    | exact superpose eq8037 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 X0 y
       have r₂ := eq8037
       grind)
    | exact resolve eq12 eq8037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8247 : ∀ X0 : G, (M.op X0 y) = (k X0 y) := by
    intro X0
    first
    | (have j0 := eq8177 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8177
  have eq8343 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2328
       have i₂ := eq8247 x
       grind)
    | exact superpose eq8247 eq2328
    | exact resolve eq2328 eq8247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2328 eq8247
  have eq8344 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8343
  have eq8371 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ (M.op y y))) := by
    first
    | (have i₁ := eq436 y (σ x)
       have i₂ := eq8344
       grind)
    | exact superpose eq8344 eq436
    | exact resolve eq436 eq8344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq436
  have eq8402 : (σ y) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq8371
       have i₂ := eq8037
       grind)
    | exact superpose eq8037 eq8371
    | exact resolve eq8371 eq8037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8037 eq8371
  have eq8405 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq8402
       have i₂ := eq8344
       grind)
    | exact superpose eq8344 eq8402
    | exact resolve eq8402 eq8344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8402
  have eq8407 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq8405
       have i₂ := eq8344
       grind)
    | exact superpose eq8344 eq8405
    | exact resolve eq8405 eq8344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8344 eq8405
  have eq8422 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq8407
       grind)
    | exact superpose eq8407 eq10
    | exact resolve eq10 eq8407
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8407
  have eq8511 : x = y := by
    first
    | (have i₁ := eq8422
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq8422
    | exact resolve eq8422 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8422
  have eq8579 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq8511
       grind)
    | exact superpose eq8511 eq16
    | exact resolve eq16 eq8511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8511
  have eq8639 : False := by grind
  exact eq8639

/-- `Equation1484`: `x = (y ◇ x) ◇ (x ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyx_pyx_pxy_pyx_Equation1484 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1484 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1484.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq82 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq184 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq82 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq13
    | (have j0 := eq13 (σ X1) (σ X0)
       have j1 := eq82 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq82 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq199 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq184 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184
  have eq200 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq199 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq199
  have eq204 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq200 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq200
    | (have j0 := eq200 X0 X1
       grind)
    | exact resolve eq200 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq205 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq204 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq602 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq205 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq205
    | exact resolve eq205 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq616 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq205 x y
       grind)
    | exact superpose eq205 eq16
    | (have j1 := eq205 x y
       grind)
    | exact resolve eq16 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq636 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ X1) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq602 X0 X1
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq602
    | (have j0 := eq602 X0 X1
       grind)
    | exact resolve eq602 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq602
  have eq637 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq636 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq636
    | exact resolve eq636 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq636
  have eq698 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq637 (τ X1) X0
       grind)
    | exact superpose eq637 eq18
    | (have j1 := eq637 (τ X1) X0
       grind)
    | exact resolve eq18 eq637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq637
  have eq888 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq698 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq698
    | exact resolve eq698 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq940 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq888 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq888
    | (have j0 := eq888 X0 X1
       grind)
    | exact resolve eq888 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq888
  have eq1025 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq616
       have i₂ := eq940 y x
       grind)
    | exact superpose eq940 eq616
    | (have j1 := eq940 (σ y) (σ x)
       grind)
    | (have r₁ := eq616
       have r₂ := eq940 y x
       grind)
    | exact resolve eq616 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1026 : y = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1025
  have eq1039 : (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1026
  have eq1053 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq616
       have i₂ := eq1039
       grind)
    | exact superpose eq1039 eq616
    | exact resolve eq616 eq1039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616 eq1039
  have eq1054 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1053
  have eq1055 : (σ y) = (M.op (σ x) (σ x)) := by grind
  clear eq1054
  have eq1101 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq1055
  have eq1117 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1101
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1101
    | exact resolve eq1101 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1101
  have eq1193 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1117
       grind)
    | exact superpose eq1117 eq16
    | exact resolve eq16 eq1117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1117
  have eq1209 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq1193
       have i₂ := eq940 y x
       grind)
    | exact superpose eq940 eq1193
    | (have j1 := eq940 y x
       grind)
    | (have r₁ := eq1193
       have r₂ := eq940 y x
       grind)
    | exact resolve eq1193 eq940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940
  have eq1210 : y = (M.op x x) := by grind
  clear eq1209
  have eq1264 : (M.op x y) = (k y x) := by grind
  clear eq1210
  have eq1278 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq1193
       have i₂ := eq1264
       grind)
    | exact superpose eq1264 eq1193
    | exact resolve eq1193 eq1264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193 eq1264
  have eq1281 : False := by grind
  exact eq1281

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_x_y_pxy_pxy_pyx_Equation1485 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X0 X1) := by
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
  have eq42 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
  have eq59 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq320 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq59 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq59 X0 X1
       grind)
    | exact superpose eq59 eq12
    | (have j1 := eq59 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq59 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq59 X0 X1
       grind)
    | exact resolve eq12 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq348 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq320 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq320
  have eq352 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq348 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq348
    | (have j0 := eq348 X0 X1
       grind)
    | exact resolve eq348 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq348
  have eq353 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq352 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352
  have eq733 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq353 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq353
    | exact resolve eq353 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq739 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq353 x y
       grind)
    | exact superpose eq353 eq16
    | (have j1 := eq353 x y
       grind)
    | exact resolve eq16 eq353
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq768 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq733 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq733
    | (have j0 := eq733 X0 X1
       grind)
    | exact resolve eq733 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq733
  have eq773 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq768 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq768
    | exact resolve eq768 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq1023 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq739
       have i₂ := eq773 x y
       grind)
    | exact superpose eq773 eq739
    | (have j1 := eq773 (σ x) (σ y)
       grind)
    | (have r₁ := eq739
       have r₂ := eq773 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq739
       have r₂ := eq773 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq739 eq773
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq739 eq773
  have eq1026 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1023
  have eq1028 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1026
       grind)
    | exact superpose eq1026 eq10
    | exact resolve eq10 eq1026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1026
  have eq1063 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1028
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1028
    | exact resolve eq1028 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028
  have eq1064 : x = y := by grind
  clear eq1063
  have eq1198 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1064
       grind)
    | exact superpose eq1064 eq16
    | exact resolve eq16 eq1064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1064
  have eq1199 : False := by grind
  exact eq1199

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_pxy_pyx_pyx_pxy_pyx_Equation1485 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) := by
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
  have eq34 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq34 (σ X0)
       grind)
    | exact superpose eq34 eq15
    | exact resolve eq15 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq36 X0
       have i₂ := eq34 X0
       grind)
    | exact superpose eq34 eq36
    | exact resolve eq36 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq36
  have eq80 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (M.op (σ X0) X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq90 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq397 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq90 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X0)
       have r₂ := eq90 X0 X0
       grind)
    | exact resolve eq12 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq399 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq13
    | (have j1 := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq90 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq90 X0 X1
       grind)
    | exact resolve eq13 eq90
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq433 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq399 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq399
  have eq438 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq433 X0 X1
       have j1 := eq80 X0 (σ X1)
       grind)
    | (have r₁ := eq433 X0 X1
       have r₂ := eq80 X0 (σ X1)
       grind)
    | exact resolve eq433 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq440 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq397 X0 X1
       have j1 := eq80 X0 (σ X1)
       grind)
    | (have r₁ := eq397 X0 X1
       have r₂ := eq80 X0 (σ X1)
       grind)
    | exact resolve eq397 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq397
  have eq450 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq438 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq438
    | (have j0 := eq438 X0 X1
       grind)
    | exact resolve eq438 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq438
  have eq451 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq450 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq450
  have eq453 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq440 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq440
    | (have j0 := eq440 X0 X1
       grind)
    | exact resolve eq440 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq461 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq451 X0 X1
       have i₂ := eq41 X0
       grind)
    | exact superpose eq41 eq451
    | (have j0 := eq451 X0 X1
       grind)
    | exact resolve eq451 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq451
  have eq462 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq453 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq453
    | (have j0 := eq453 X0 X1
       grind)
    | exact resolve eq453 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq453
  have eq463 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq462 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq466 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq463 X0 X1
       have j1 := eq461 X0 X1
       grind)
    | (have r₁ := eq463 X0 X1
       have r₂ := eq461 X0 X1
       grind)
    | exact resolve eq463 eq461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq461 eq463
  have eq468 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq466 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq466
    | exact resolve eq466 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq479 : (σ (M.op x y)) ≠ (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq466 x y
       grind)
    | exact superpose eq466 eq16
    | exact resolve eq16 eq466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq466
  have eq579 : ∀ X0 X1 : G, (k X1 (σ (τ X0))) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 (τ X0)
       have i₂ := eq468 X0 (τ X1)
       grind)
    | exact superpose eq468 eq17
    | exact resolve eq17 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq468
  have eq601 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq579 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq579
    | exact resolve eq579 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq579
  have eq612 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq601 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq601
    | exact resolve eq601 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq631 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq479
       have i₂ := eq612 x y
       grind)
    | exact superpose eq612 eq479
    | exact resolve eq479 eq612
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq479 eq612
  have eq632 : False := by grind
  exact eq632

/-- `Equation1485`: `x = (y ◇ x) ◇ (x ◇ (z ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyx_x_pyx_x_pyx_Equation1485 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law1485 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law1485.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X0) (M.op X0 (M.op X2 X1))) = X0 := by
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
  have eq50 : ∀ X0 : G, y = (M.op (M.op x y) (M.op y (M.op X0 x))) := by
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
  have eq66 : y ≠ (M.op x y) ∨ (k x y) = (M.op y x) := by
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
  have eq78 : y ≠ (M.op x y) ∨ x = (M.op y x) ∨ y = (k y x) := by
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
  have eq79 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X0
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq96 y x
       grind)
    | exact superpose eq96 eq75
    | (have j1 := eq96 y x
       grind)
    | exact resolve eq75 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq107
    | exact resolve eq107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq119
    | exact resolve eq119 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq121
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq121
    | exact resolve eq121 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq121
  have eq125 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq122 eq96
    | (have j0 := eq96 (σ y) (σ x)
       grind)
    | exact resolve eq96 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq126 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq125
    | exact resolve eq125 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq129 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq126
       have r₂ := eq27
       grind)
    | exact resolve eq126 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq126
  have eq131 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq129
    | exact resolve eq129 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129
  have eq133 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq131 eq27
    | exact resolve eq27 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq927 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq131 eq79
    | (have r₁ := eq79
       have r₂ := eq131
       grind)
    | exact resolve eq79 eq131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq131
  have eq928 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq927
  have eq1016 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq928 eq122
    | exact resolve eq122 eq928
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq928
  have eq1020 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq1016
  have eq1025 : (σ x) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq1020
       have r₂ := eq133
       grind)
    | exact resolve eq1020 eq133
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq1020
  have eq1046 : (σ x) ≠ (σ x) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1025 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1025
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq1025
       grind)
    | exact resolve eq13 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025
  have eq1059 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq1046
  have eq1077 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq1059
    | exact resolve eq1059 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1059
  have eq1481 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1077 eq122
    | exact resolve eq122 eq1077
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq1077
  have eq1484 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1481
  have eq1489 : y = (M.op x y) := by
    first
    | (have r₁ := eq1484
       have r₂ := eq27
       grind)
    | exact resolve eq1484 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1484
  have eq1491 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq1489 eq20
    | exact resolve eq20 eq1489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq1493 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 x))) := by
    intro X0
    first
    | exact superpose eq1489 eq50
    | exact resolve eq50 eq1489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1495 : y ≠ y ∨ (k x y) = (M.op y x) := by
    first
    | exact superpose eq1489 eq66
    | (have r₁ := eq66
       have r₂ := eq1489
       grind)
    | exact resolve eq66 eq1489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq1497 : y ≠ y ∨ x = (M.op y x) ∨ y = (k y x) := by
    first
    | exact superpose eq1489 eq78
    | (have r₁ := eq78
       have r₂ := eq1489
       grind)
    | exact resolve eq78 eq1489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq1489
  have eq1501 : y = (k y x) ∨ x = (M.op y x) := by grind
  clear eq1497
  have eq1502 : (k x y) = (M.op y x) := by grind
  clear eq1495
  have eq1508 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq1491
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1491
    | exact resolve eq1491 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1491
  have eq1584 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq1508 eq26
    | exact resolve eq26 eq1508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq1677 : (k (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq1502
       grind)
    | exact superpose eq1502 eq44
    | exact resolve eq44 eq1502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq1502
  have eq1678 : (k (σ x) (σ (M.op x y))) = (σ (M.op y x)) := by
    first
    | exact superpose eq1508 eq1677
    | exact resolve eq1677 eq1508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677
  have eq2002 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq75
       have i₂ := eq1501
       grind)
    | exact superpose eq1501 eq75
    | exact resolve eq75 eq1501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq1501
  have eq2009 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1508 eq2002
    | exact resolve eq2002 eq1508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2002
  have eq2011 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq2009
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2009
    | exact resolve eq2009 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2009
  have eq2012 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1508 eq2011
    | exact resolve eq2011 eq1508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2011
  have eq2016 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op y x) := by
    first
    | exact superpose eq2012 eq96
    | (have j0 := eq96 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq96 eq2012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2012
  have eq2017 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ x = (M.op y x) := by grind
  clear eq2016
  have eq2019 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) := by
    first
    | exact superpose eq1584 eq2017
    | exact resolve eq2017 eq1584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2017
  have eq2022 : x = (M.op y x) := by
    first
    | (have r₁ := eq2019
       have r₂ := eq27
       grind)
    | exact resolve eq2019 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2019
  have eq2027 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq1678
       have i₂ := eq2022
       grind)
    | exact superpose eq2022 eq1678
    | exact resolve eq1678 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1678
  have eq2036 : y = (M.op y (M.op y x)) := by
    first
    | (have i₁ := eq1493 y
       have i₂ := eq2022
       grind)
    | exact superpose eq2022 eq1493
    | exact resolve eq1493 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1493
  have eq2064 : y = (M.op y x) := by
    first
    | (have i₁ := eq2036
       have i₂ := eq2022
       grind)
    | exact superpose eq2022 eq2036
    | exact resolve eq2036 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2036
  have eq2069 : (σ x) = (k (σ x) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2027
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2027
    | exact resolve eq2027 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2027
  have eq2075 : x = y := by
    first
    | (have i₁ := eq2064
       have i₂ := eq2022
       grind)
    | exact superpose eq2022 eq2064
    | exact resolve eq2064 eq2022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2022 eq2064
  have eq2092 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq2075
       grind)
    | exact superpose eq2075 eq24
    | exact resolve eq24 eq2075
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2075
  have eq2129 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1508 eq2092
    | exact resolve eq2092 eq1508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1508 eq2092
  have eq2143 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2129
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2129
    | exact resolve eq2129 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2129
  have eq2298 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2143 eq1584
    | exact resolve eq1584 eq2143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1584
  have eq2325 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2143 eq2069
    | exact resolve eq2069 eq2143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2069 eq2143
  have eq2411 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2325 eq96
    | (have j0 := eq96 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq96 eq2325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq2325
  have eq2412 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2411
  have eq2637 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2412 eq2298
    | exact resolve eq2298 eq2412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2298 eq2412
  have eq2638 : False := by grind
  exact eq2638
