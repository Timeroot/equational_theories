import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(X,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pxx_y_pyx_pxx_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op a a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq26 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X0 X1)) := by
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
  have eq35 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X1
       have r₂ := eq12 X1 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 X1 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq58
    | (have j0 := eq58 (σ X0) (σ X1)
       grind)
    | exact resolve eq58 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq35 (τ X0)
       grind)
    | exact superpose eq35 eq19
    | exact resolve eq19 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq85 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq84 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq84
    | exact resolve eq84 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq85
    | exact resolve eq85 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq85
  have eq97 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq93 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq93
    | exact resolve eq93 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq107 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 (M.op X0 X1)
       have i₂ := eq26 X0 X1
       grind)
    | exact superpose eq26 eq12
    | (have j0 := eq12 X0 X1
       grind)
    | (have r₁ := eq12 X1 (M.op X1 X1)
       have r₂ := eq26 X1 X1
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (k X0 (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq107 X0 X1
       have j1 := eq58 X0 (M.op X0 X1)
       grind)
    | (have r₁ := eq107 X0 X0
       have r₂ := eq58 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq107 X0 X1
       have r₂ := eq58 X0 (M.op X0 X1)
       grind)
    | exact resolve eq107 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq140 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq69 y x
       grind)
    | exact superpose eq69 eq16
    | (have j1 := eq69 y x
       grind)
    | exact resolve eq16 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq168 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq26 (σ X0) (σ X0)
       have i₂ := eq97 X0
       grind)
    | exact superpose eq97 eq26
    | exact resolve eq26 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq565 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq140
       have i₂ := eq97 y
       grind)
    | exact superpose eq97 eq140
    | exact resolve eq140 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq140
  have eq566 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq565
       have i₂ := eq58 y x
       grind)
    | exact superpose eq58 eq565
    | (have j1 := eq58 y x
       grind)
    | exact resolve eq565 eq58
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq569 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq566
  have eq597 : (M.op x y) = (k y x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq110 y y
       have i₂ := eq569
       grind)
    | exact superpose eq569 eq110
    | exact resolve eq110 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq766 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq565
       have i₂ := eq597
       grind)
    | exact superpose eq597 eq565
    | exact resolve eq565 eq597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565 eq597
  have eq767 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq766
  have eq768 : (σ x) = (σ (M.op y y)) := by grind
  clear eq767
  have eq771 : (σ x) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq168 y
       have i₂ := eq768
       grind)
    | exact superpose eq768 eq168
    | exact resolve eq168 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq168
  have eq772 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq768
       grind)
    | exact superpose eq768 eq10
    | exact resolve eq10 eq768
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq768
  have eq807 : x = (M.op y y) := by
    first
    | (have i₁ := eq772
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq772
    | exact resolve eq772 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq772
  have eq886 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq110 y y
       have i₂ := eq807
       grind)
    | exact superpose eq807 eq110
    | exact resolve eq110 eq807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq807
  have eq1092 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq110 (σ y) (σ x)
       have i₂ := eq771
       grind)
    | exact superpose eq771 eq110
    | exact resolve eq110 eq771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq771
  have eq1093 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have i₁ := eq1092
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1092
    | exact resolve eq1092 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1092
  have eq1098 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1093
       have i₂ := eq886
       grind)
    | exact superpose eq886 eq1093
    | exact resolve eq1093 eq886
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq886 eq1093
  have eq1100 : False := by grind
  exact eq1100

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(X,Y) then m(Y,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pxy_pyx_x_pyx_x_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op a b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op a b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op a b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (M.op X0 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = X0 := by
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
  have eq50 : ∀ X0 : G, x = (M.op (M.op (M.op (M.op x y) X0) X0) x) := by
    intro X0
    first
    | (have i₁ := eq14 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x y X0
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq51 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (M.op (σ x) (σ y)) X0) X0) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) (σ y) X0
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X1) X2) X2)) ∨ (k X0 (M.op (M.op (M.op X0 X1) X2) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       grind)
    | (have r₁ := eq12 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       have r₂ := eq14 X0 X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X1) X2) X2)) ∨ (k X0 (M.op (M.op (M.op X0 X1) X2) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq79 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq86 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq11 (M.op X0 X0) X0
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq22 eq36
  have eq116 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq92
       have i₂ := eq86 y x
       grind)
    | exact superpose eq86 eq92
    | (have j1 := eq86 y x
       grind)
    | exact resolve eq92 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq126 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq124
    | exact resolve eq124 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq127 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq126
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq126
    | exact resolve eq126 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq126
  have eq196 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq127 eq86
    | (have j0 := eq86 (σ y) (σ x)
       grind)
    | exact resolve eq86 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq196
    | exact resolve eq196 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq200 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq197
       have r₂ := eq27
       grind)
    | exact resolve eq197 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq202 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq200
    | exact resolve eq200 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq200
  have eq204 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq202 eq27
    | exact resolve eq27 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ y) X0) X0) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq202 eq51
    | exact resolve eq51 eq202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq202
  have eq943 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = (k X0 (M.op (M.op (M.op X0 X1) X2) X2)) ∨ (k X0 (M.op (M.op (M.op X0 X1) X2) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       have i₂ := eq80 X0 X1 X2
       grind)
    | exact superpose eq80 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq80 X0 X1 X2
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       have r₂ := eq80 X0 X1 X2
       grind)
    | exact resolve eq13 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq977 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) X2) X0) = (k X0 (M.op (M.op (M.op X0 X1) X2) X2)) ∨ (k X0 (M.op (M.op (M.op X0 X1) X2) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq943 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq943
  have eq978 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X0 X1) X2) X2)) = X0 ∨ (k X0 (M.op (M.op (M.op X0 X1) X2) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq977 X0 X1 X2
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq977
    | (have j0 := eq977 X0 X1 X2
       grind)
    | exact resolve eq977 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977
  have eq979 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X0 X1) X2) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq978 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq978
  have eq2144 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq264 eq979
    | exact resolve eq979 eq264
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264
  have eq2159 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq2144 eq127
    | exact resolve eq127 eq2144
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127 eq2144
  have eq2163 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq2159
  have eq2168 : y = (M.op x y) := by
    first
    | (have r₁ := eq2163
       have r₂ := eq204
       grind)
    | exact resolve eq2163 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq2163
  have eq2171 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq2168 eq20
    | exact resolve eq20 eq2168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq2173 : ∀ X0 : G, x = (M.op (M.op (M.op y X0) X0) x) := by
    intro X0
    first
    | exact superpose eq2168 eq50
    | exact resolve eq50 eq2168
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50 eq2168
  have eq2189 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq2171
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2171
    | exact resolve eq2171 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2171
  have eq2194 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2189 eq26
    | exact resolve eq26 eq2189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2326 : y = (k y x) := by
    first
    | (have i₁ := eq979 y x x
       have i₂ := eq2173 x
       grind)
    | exact superpose eq2173 eq979
    | exact resolve eq979 eq2173
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq979 eq2173
  have eq2413 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq92
       have i₂ := eq2326
       grind)
    | exact superpose eq2326 eq92
    | exact resolve eq92 eq2326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq2326
  have eq2420 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq2189 eq2413
    | exact resolve eq2413 eq2189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2413
  have eq2422 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq2420
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2420
    | exact resolve eq2420 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2420
  have eq2423 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq2189 eq2422
    | exact resolve eq2422 eq2189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2189 eq2422
  have eq2426 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq2423 eq86
    | (have j0 := eq86 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq86 eq2423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq2423
  have eq2427 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) := by grind
  clear eq2426
  have eq2429 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2194 eq2427
    | exact resolve eq2427 eq2194
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2194 eq2427
  have eq2432 : False := by grind
  exact eq2432

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pxy_pyx_pxx_pxy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
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
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq65 (σ X0)
       grind)
    | exact superpose eq65 eq10
    | exact resolve eq10 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq67
    | exact resolve eq67 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq11
    | (have j0 := eq11 (σ X1) (σ X0)
       grind)
    | exact resolve eq11 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq100 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq104 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq100
       have i₂ := eq65 sF3
       grind)
    | exact superpose eq65 eq100
    | exact resolve eq100 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq106 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq65 y
       grind)
    | exact superpose eq65 eq104
    | exact resolve eq104 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq104
  have eq108 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq99
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq99 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq114 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
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
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq116 : (M.op x y) = (M.op y x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq115
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq115
    | exact resolve eq115 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq117 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq116
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq116
    | exact resolve eq116 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq728 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq76
    | (have j0 := eq76 X0 X1
       grind)
    | exact resolve eq76 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq833 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq728 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq728 X0 X1
       grind)
    | exact superpose eq728 eq12
    | (have j0 := eq12 (σ X1) (σ X0)
       have j1 := eq728 X1 X0
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq728 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq728 X0 X1
       grind)
    | exact resolve eq12 eq728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq728
  have eq844 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq833 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq833
  have eq850 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq844 X0 X1
       have i₂ := eq72 X1
       grind)
    | exact superpose eq72 eq844
    | (have j0 := eq844 X0 X1
       grind)
    | exact resolve eq844 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq844
  have eq851 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq850 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq850
  have eq871 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq851 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq851
    | (have j0 := eq851 X0 X1
       grind)
    | exact resolve eq851 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq872 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq871 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq871
  have eq4845 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq872 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq20296 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq117 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20297 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq20296
    | exact resolve eq20296 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20296
  have eq20308 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq20297
       have r₂ := eq27
       grind)
    | exact resolve eq20297 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20297
  have eq20312 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq20308
    | exact resolve eq20308 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20308
  have eq20314 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq20312
    | exact resolve eq20312 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20312
  have eq20325 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq20314 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq20314
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq20314
       grind)
    | exact resolve eq13 eq20314
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20314
  have eq21717 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq20325
    | (have j0 := eq20325 (σ x)
       grind)
    | (have r₁ := eq20325 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq20325 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20325
  have eq21721 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq21717
  have eq21730 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq21721 eq117
    | exact resolve eq117 eq21721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21721
  have eq21738 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq21730
  have eq21740 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq21738
       have r₂ := eq27
       grind)
    | exact resolve eq21738 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21738
  have eq21742 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq21740 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq21740
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq21740
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq21740
       grind)
    | exact resolve eq12 eq21740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21740
  have eq21787 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq21742
       have r₂ := eq26
       grind)
    | exact resolve eq21742 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21742
  have eq21789 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq21787
    | exact resolve eq21787 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21787
  have eq22270 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq21789 eq117
    | exact resolve eq117 eq21789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21789
  have eq22278 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq22270
  have eq22280 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq22278
       have r₂ := eq27
       grind)
    | exact resolve eq22278 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22278
  have eq22294 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) X0) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | exact superpose eq22280 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq22280
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq22280
       grind)
    | exact resolve eq13 eq22280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22280
  have eq23718 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq22294
    | (have j0 := eq22294 (σ x)
       grind)
    | (have r₁ := eq22294 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq22294 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22294
  have eq23725 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq23718
  have eq23735 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq23725 eq117
    | exact resolve eq117 eq23725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117 eq23725
  have eq23743 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq23735
  have eq23745 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq23743
       have r₂ := eq27
       grind)
    | exact resolve eq23743 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23743
  have eq23749 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq106
       have i₂ := eq23745
       grind)
    | exact superpose eq23745 eq106
    | exact resolve eq106 eq23745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23758 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) ∨ (M.op x y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq13 y x
       have i₂ := eq23745
       grind)
    | exact superpose eq23745 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq23745
       grind)
    | exact resolve eq13 eq23745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23745
  have eq23838 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq23749
    | exact resolve eq23749 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23749
  have eq26014 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq23758 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq23758
    | (have j0 := eq23758 x
       grind)
    | (have r₁ := eq23758 x
       have r₂ := eq18
       grind)
    | exact resolve eq23758 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23758
  have eq26022 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq26014
  have eq26030 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq99
       have i₂ := eq26022
       grind)
    | exact superpose eq26022 eq99
    | exact resolve eq99 eq26022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26022
  have eq26048 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq26030
    | exact resolve eq26030 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26030
  have eq26067 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26048 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26048
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26074 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq26067
    | exact resolve eq26067 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26067
  have eq26085 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq26074
       have r₂ := eq27
       grind)
    | exact resolve eq26074 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26074
  have eq26089 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq26085
    | exact resolve eq26085 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26085
  have eq26091 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq26089
    | exact resolve eq26089 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26089
  have eq26760 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26091 eq23838
    | exact resolve eq23838 eq26091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26091
  have eq26844 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq26760
  have eq26855 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq26844
       have r₂ := eq27
       grind)
    | exact resolve eq26844 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26844
  have eq26857 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26855 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq26855
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq26855
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq26855
       grind)
    | exact resolve eq12 eq26855
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26855
  have eq26914 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq26857
       have r₂ := eq26
       grind)
    | exact resolve eq26857 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26857
  have eq26916 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq26914
    | exact resolve eq26914 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26914
  have eq27781 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26916 eq26048
    | exact resolve eq26048 eq26916
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26048 eq26916
  have eq27787 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq27781
  have eq27795 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq27787
       have r₂ := eq27
       grind)
    | exact resolve eq27787 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27787
  have eq27813 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq27795 eq23838
    | exact resolve eq23838 eq27795
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23838 eq27795
  have eq27899 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq27813
  have eq27910 : (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq27899
       have r₂ := eq27
       grind)
    | exact resolve eq27899 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27899
  have eq27912 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq27910
       grind)
    | exact superpose eq27910 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq27910
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq27910
       grind)
    | exact resolve eq12 eq27910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27910
  have eq27969 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (k y x) := by
    first
    | (have r₁ := eq27912
       have r₂ := eq18
       grind)
    | exact resolve eq27912 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27912
  have eq27971 : (M.op x y) = (k y x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq27969
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq27969
    | exact resolve eq27969 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27969
  have eq28306 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq99
       have i₂ := eq27971
       grind)
    | exact superpose eq27971 eq99
    | exact resolve eq99 eq27971
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq27971
  have eq28326 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq28306
    | exact resolve eq28306 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28306
  have eq28377 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq28326 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq28326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28384 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq28377
    | exact resolve eq28377 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28377
  have eq28395 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq28384
       have r₂ := eq27
       grind)
    | exact resolve eq28384 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28384
  have eq28399 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq28395
    | exact resolve eq28395 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28395
  have eq28401 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq28399
    | exact resolve eq28399 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28399
  have eq40770 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq28401 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq28401
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq28401
       grind)
    | exact resolve eq13 eq28401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28401
  have eq548028 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq40770
    | (have j0 := eq40770 (σ x)
       grind)
    | (have r₁ := eq40770 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq40770 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40770
  have eq548047 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq548028
  have eq548091 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq548047 eq28326
    | exact resolve eq28326 eq548047
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548047
  have eq548323 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by grind
  clear eq548091
  have eq548333 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq548323
       have r₂ := eq27
       grind)
    | exact resolve eq548323 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548323
  have eq548347 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq548333 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq548333
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq548333
       grind)
    | exact resolve eq12 eq548333
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548333
  have eq548458 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq548347
       have r₂ := eq26
       grind)
    | exact resolve eq548347 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548347
  have eq548460 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq548458
    | exact resolve eq548458 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548458
  have eq549816 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq548460 eq28326
    | exact resolve eq28326 eq548460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq548460
  have eq550048 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq549816
  have eq550058 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq550048
       have r₂ := eq27
       grind)
    | exact resolve eq550048 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550048
  have eq550111 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) X0) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq550058 eq13
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq550058
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq550058
       grind)
    | exact resolve eq13 eq550058
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550058
  have eq552602 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq550111
    | (have j0 := eq550111 (σ x)
       grind)
    | (have r₁ := eq550111 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq550111 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550111
  have eq552623 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq552602
  have eq552669 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq552623 eq28326
    | exact resolve eq28326 eq552623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28326 eq552623
  have eq552901 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq552669
  have eq552911 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq552901
       have r₂ := eq27
       grind)
    | exact resolve eq552901 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552901
  have eq552918 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq106
       have i₂ := eq552911
       grind)
    | exact superpose eq552911 eq106
    | exact resolve eq106 eq552911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq553109 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y x
       have i₂ := eq552911
       grind)
    | exact superpose eq552911 eq13
    | (have r₁ := eq13 y x
       have r₂ := eq552911
       grind)
    | exact resolve eq13 eq552911
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552911
  have eq553294 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq552918
    | exact resolve eq552918 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552918
  have eq555135 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq553109 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq553109
    | (have j0 := eq553109 x
       grind)
    | (have r₁ := eq553109 x
       have r₂ := eq18
       grind)
    | exact resolve eq553109 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq553109
  have eq555145 : (M.op x y) = (k y x) := by grind
  clear eq555135
  have eq555221 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq4845 x y
       have i₂ := eq555145
       grind)
    | exact superpose eq555145 eq4845
    | (have j0 := eq4845 x y
       grind)
    | exact resolve eq4845 eq555145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4845 eq555145
  have eq555228 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq555221
       have i₂ := eq106
       grind)
    | exact superpose eq106 eq555221
    | exact resolve eq555221 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555221
  have eq555256 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq553294 eq555228
    | (have r₁ := eq555228
       have r₂ := eq553294
       grind)
    | exact resolve eq555228 eq553294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555228
  have eq555271 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq555256
       have r₂ := eq20
       grind)
    | exact resolve eq555256 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq555256
  have eq555283 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq555271
       have i₂ := eq106
       grind)
    | exact superpose eq106 eq555271
    | exact resolve eq555271 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq555271
  have eq555295 : (M.op (σ x) (σ y)) = (σ (M.op x y)) := by
    first
    | exact superpose eq553294 eq555283
    | exact resolve eq555283 eq553294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553294 eq555283
  have eq555307 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq555295
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq555295
    | exact resolve eq555295 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq555295
  have eq555319 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq555307
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq555307
    | exact resolve eq555307 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq555307
  have eq555331 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq555319
    | exact resolve eq555319 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq555319
  have eq555341 : False := by grind
  exact eq555341

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_x_pxx_x_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 := by
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
  have eq67 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X2) (M.op (M.op X0 X1) X2)) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 (M.op (M.op X0 X1) X2)
       have i₂ := eq63 (M.op X0 X1) X2
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq68 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 (M.op (M.op (M.op X0 X1) X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq12
    | (have j0 := eq12 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       grind)
    | exact resolve eq12 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq69 (σ X0)
       grind)
    | exact superpose eq69 eq15
    | exact resolve eq15 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq72 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq72
    | exact resolve eq72 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq72
  have eq99 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (M.op (σ (M.op X0 X0)) X1) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq9
    | exact resolve eq9 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq12
    | exact resolve eq12 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq527 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 (M.op (M.op (M.op X0 X1) X2) X2)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq13
    | (have j0 := eq13 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       grind)
    | (have r₁ := eq13 X0 (M.op (M.op (M.op X0 X1) X2) X2)
       have r₂ := eq9 X0 X1 X2
       grind)
    | exact resolve eq13 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq544 : ∀ X0 X1 X2 : G, (k X0 (M.op (M.op (M.op X0 X1) X2) X2)) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq527 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq527
  have eq791 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq809 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq791 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq1242 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq809 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq1249 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq1242 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq1242 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq1242 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq1242 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1242
  have eq1305 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq1249 X1 (τ X0)
       grind)
    | exact superpose eq1249 eq18
    | (have j1 := eq1249 X1 (τ X0)
       grind)
    | exact resolve eq18 eq1249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq1308 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1249 (σ X1) (σ X0)
       grind)
    | exact superpose eq1249 eq15
    | (have j1 := eq1249 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq1249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1249
  have eq1418 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1305 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1305
    | exact resolve eq1305 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1305
  have eq1480 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1418 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1418
    | (have j0 := eq1418 X0 X1
       grind)
    | exact resolve eq1418 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1418
  have eq1703 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1308 x y
       grind)
    | exact superpose eq1308 eq16
    | (have j1 := eq1308 x y
       grind)
    | exact resolve eq16 eq1308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1744 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1308 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1308
  have eq1799 : ∀ X0 X1 X2 : G, (σ X0) ≠ (σ X0) ∨ (σ X0) = (M.op (σ (M.op (M.op (M.op X0 X1) X2) X2)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1744 (M.op (M.op (M.op X0 X1) X2) X2) X0
       have i₂ := eq544 X0 X1 X2
       grind)
    | exact superpose eq544 eq1744
    | (have j0 := eq1744 (M.op (M.op (M.op X0 X1) X2) X2) X0
       have j1 := eq544 X0 X1 X2
       grind)
    | exact resolve eq1744 eq544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq1807 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (σ (τ (k X0 X1))) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1744 (τ X1) (τ X0)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq1744
    | (have j0 := eq1744 (τ X1) (τ X0)
       grind)
    | exact resolve eq1744 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq1813 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ (M.op (M.op (M.op X0 X1) X2) X2)) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1 X2
    first
    | (have j0 := eq1799 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1799
  have eq1816 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 X1) ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1807 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq1807
    | (have j0 := eq1807 X0 X1
       grind)
    | exact resolve eq1807 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1807
  have eq1819 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X1)) (σ (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1816 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1816
    | (have j0 := eq1816 X0 X1
       grind)
    | exact resolve eq1816 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1816
  have eq1820 : ∀ X0 X1 : G, (M.op (σ (τ X1)) X0) = X0 ∨ (k X0 X1) ≠ X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1819 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1819
    | (have j0 := eq1819 X0 X1
       grind)
    | exact resolve eq1819 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1819
  have eq1821 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1820 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq1820
    | (have j0 := eq1820 X0 X1
       grind)
    | exact resolve eq1820 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1820
  have eq1930 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1703
       have i₂ := eq1480 x y
       grind)
    | exact superpose eq1480 eq1703
    | (have j1 := eq1480 (σ x) (σ y)
       grind)
    | (have r₁ := eq1703
       have r₂ := eq1480 x y
       grind)
    | exact resolve eq1703 eq1480
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1703
  have eq1931 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1930
  have eq1935 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1931
       grind)
    | exact superpose eq1931 eq16
    | exact resolve eq16 eq1931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1938 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ y) X0) X0) (σ x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) (σ y) X0
       have i₂ := eq1931
       grind)
    | exact superpose eq1931 eq9
    | exact resolve eq9 eq1931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1939 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq1931
       grind)
    | exact superpose eq1931 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq1931
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq1931
       grind)
    | exact resolve eq13 eq1931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1931
  have eq1945 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq1939
  have eq1949 : (σ y) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1945
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq1945
    | exact resolve eq1945 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1945
  have eq1952 : (σ y) = (σ (k y x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1949
       have i₂ := eq83 y
       grind)
    | exact superpose eq83 eq1949
    | exact resolve eq1949 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1949
  have eq1953 : (σ x) = (M.op (M.op (σ (M.op y y)) (σ y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1938 (σ y)
       have i₂ := eq83 y
       grind)
    | exact superpose eq83 eq1938
    | exact resolve eq1938 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1938
  have eq4040 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1480 x y
       have i₂ := eq1952
       grind)
    | exact superpose eq1952 eq1480
    | (have j0 := eq1480 x y
       grind)
    | exact resolve eq1480 eq1952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1480 eq1952
  have eq4079 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (σ (M.op y y)) := by grind
  clear eq4040
  have eq4105 : (σ y) = (σ (M.op y y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4079
       have r₂ := eq1935
       grind)
    | exact resolve eq4079 eq1935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1935 eq4079
  have eq4110 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1953
       have i₂ := eq4105
       grind)
    | exact superpose eq4105 eq1953
    | exact resolve eq1953 eq4105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1953
  have eq4120 : (M.op y y) = (τ (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq4105
       grind)
    | exact superpose eq4105 eq10
    | exact resolve eq10 eq4105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4158 : (σ x) = (M.op (M.op (σ y) (σ y)) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq4110
  have eq4176 : y = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4120
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq4120
    | exact resolve eq4120 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4120
  have eq4180 : (σ x) = (M.op (σ (M.op y y)) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4158
       have i₂ := eq83 y
       grind)
    | exact superpose eq83 eq4158
    | exact resolve eq4158 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4158
  have eq4187 : ∀ X0 X1 : G, y ≠ y ∨ y = (k y (M.op (M.op (M.op y X0) X1) X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have i₁ := eq68 y X1 x
       have i₂ := eq4176
       grind)
    | exact superpose eq4176 eq68
    | (have r₁ := eq68 y X1 x
       have r₂ := eq4176
       grind)
    | exact resolve eq68 eq4176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq4218 : ∀ X0 X1 : G, y = (k y (M.op (M.op (M.op y X0) X1) X1)) ∨ y = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq4187 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4187
  have eq4503 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq99 y (σ x)
       have i₂ := eq4180
       grind)
    | exact superpose eq4180 eq99
    | exact resolve eq99 eq4180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq4180
  have eq4528 : (σ y) = (M.op (σ (M.op x x)) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4503
       have i₂ := eq83 x
       grind)
    | exact superpose eq83 eq4503
    | exact resolve eq4503 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq4503
  have eq4740 : (σ y) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ y) (σ (M.op x x))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq100 y (σ (M.op x x))
       have i₂ := eq4528
       grind)
    | exact superpose eq4528 eq100
    | (have j0 := eq100 y (σ (M.op x x))
       grind)
    | exact resolve eq100 eq4528
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq4528
  have eq4760 : (σ (M.op y y)) = (k (σ y) (σ (M.op x x))) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq4740
       have r₂ := eq4105
       grind)
    | exact resolve eq4740 eq4105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4105 eq4740
  have eq4765 : (σ (M.op y y)) = (σ (k y (M.op x x))) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq4760
       have i₂ := eq15 y (M.op x x)
       grind)
    | exact superpose eq15 eq4760
    | exact resolve eq4760 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4760
  have eq6239 : (τ (σ (M.op y y))) = (k y (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 (k y (M.op x x))
       have i₂ := eq4765
       grind)
    | exact superpose eq4765 eq10
    | exact resolve eq10 eq4765
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4765
  have eq6298 : (M.op y y) = (k y (M.op x x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6239
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq6239
    | exact resolve eq6239 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6239
  have eq6315 : y ≠ (M.op y y) ∨ y = (M.op (M.op x x) y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1821 y (M.op x x)
       have i₂ := eq6298
       grind)
    | exact superpose eq6298 eq1821
    | (have j0 := eq1821 y (M.op x x)
       grind)
    | exact resolve eq1821 eq6298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1821 eq6298
  have eq6326 : y = (M.op (M.op x x) y) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq6315
       have r₂ := eq4176
       grind)
    | exact resolve eq6315 eq4176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6315
  have eq6330 : x = (M.op (M.op y y) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq67 x x y
       have i₂ := eq6326
       grind)
    | exact superpose eq6326 eq67
    | exact resolve eq67 eq6326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6336 : ∀ X0 : G, (M.op x x) = (M.op (M.op (M.op y X0) X0) (M.op x x)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 (M.op x x) y X0
       have i₂ := eq6326
       grind)
    | exact superpose eq6326 eq9
    | exact resolve eq9 eq6326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6326
  have eq6350 : x = (M.op y x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6330
       have i₂ := eq4176
       grind)
    | exact superpose eq4176 eq6330
    | exact resolve eq6330 eq4176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4176 eq6330
  have eq6373 : x = (M.op y x) ∨ y = (M.op x y) := by grind
  clear eq6350
  have eq6376 : ∀ X0 : G, y = (k y (M.op (M.op x X0) X0)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq4218 x X0
       have i₂ := eq6373
       grind)
    | exact superpose eq6373 eq4218
    | exact resolve eq4218 eq6373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4218
  have eq6380 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) X0) y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq6373
       grind)
    | exact superpose eq6373 eq9
    | exact resolve eq9 eq6373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6395 : ∀ X0 : G, y = (k y (M.op (M.op x X0) X0)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq6376 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6376
  have eq13318 : (M.op x x) = (M.op (M.op x x) (M.op x x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6336 x
       have i₂ := eq6373
       grind)
    | exact superpose eq6373 eq6336
    | exact resolve eq6336 eq6373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6336 eq6373
  have eq13360 : (M.op x x) = (M.op (M.op x x) (M.op x x)) ∨ y = (M.op x y) := by grind
  clear eq13318
  have eq13377 : x = (M.op (M.op (M.op x x) (M.op x x)) x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq67 x x (M.op x x)
       have i₂ := eq13360
       grind)
    | exact superpose eq13360 eq67
    | exact resolve eq67 eq13360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13447 : x = (M.op (M.op x x) x) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13377
       have i₂ := eq13360
       grind)
    | exact superpose eq13360 eq13377
    | exact resolve eq13377 eq13360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13360 eq13377
  have eq13474 : x = (M.op (M.op x x) x) ∨ y = (M.op x y) := by grind
  clear eq13447
  have eq13481 : y = (M.op x y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6380 x
       have i₂ := eq13474
       grind)
    | exact superpose eq13474 eq6380
    | exact resolve eq6380 eq13474
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6380 eq13474
  have eq13510 : y = (M.op x y) := by grind
  clear eq13481
  have eq13516 : ∀ X0 : G, x = (M.op (M.op (M.op y X0) X0) x) := by
    intro X0
    first
    | (have i₁ := eq9 x y X0
       have i₂ := eq13510
       grind)
    | exact superpose eq13510 eq9
    | exact resolve eq9 eq13510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13522 : ∀ X0 : G, x = (M.op (M.op (M.op y X0) (M.op y X0)) x) := by
    intro X0
    first
    | (have i₁ := eq67 x y x
       have i₂ := eq13510
       grind)
    | exact superpose eq13510 eq67
    | exact resolve eq67 eq13510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq13540 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq1813 y x x
       have i₂ := eq13516 x
       grind)
    | exact superpose eq13516 eq1813
    | (have j0 := eq1813 y x x
       grind)
    | exact resolve eq1813 eq13516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1813 eq13516
  have eq13680 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13540
       grind)
    | exact superpose eq13540 eq16
    | exact resolve eq16 eq13540
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13540
  have eq13703 : (σ y) ≠ (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq13680
       have i₂ := eq13510
       grind)
    | exact superpose eq13510 eq13680
    | exact resolve eq13680 eq13510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13680
  have eq13704 : y = (M.op y y) := by grind
  clear eq13703
  have eq13779 : x = (M.op (M.op y y) x) := by
    first
    | (have i₁ := eq13522 y
       have i₂ := eq13704
       grind)
    | exact superpose eq13704 eq13522
    | exact resolve eq13522 eq13704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13781 : ∀ X0 : G, y ≠ (M.op X0 y) ∨ y = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq12 y x
       have i₂ := eq13704
       grind)
    | exact superpose eq13704 eq12
    | exact resolve eq12 eq13704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13829 : x = (M.op y x) := by
    first
    | (have i₁ := eq13779
       have i₂ := eq13704
       grind)
    | exact superpose eq13704 eq13779
    | exact resolve eq13779 eq13704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13704 eq13779
  have eq13862 : x = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq13522 x
       have i₂ := eq13829
       grind)
    | exact superpose eq13829 eq13522
    | exact resolve eq13522 eq13829
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13522 eq13829
  have eq13916 : y = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq6395 x
       have i₂ := eq13862
       grind)
    | exact superpose eq13862 eq6395
    | exact resolve eq6395 eq13862
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6395 eq13862
  have eq13945 : y = (k y x) := by
    first
    | (have j1 := eq13781 x
       grind)
    | (have r₁ := eq13916
       have r₂ := eq13781 x
       grind)
    | exact resolve eq13916 eq13781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13781 eq13916
  have eq13965 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1744 x y
       have i₂ := eq13945
       grind)
    | exact superpose eq13945 eq1744
    | (have j0 := eq1744 x y
       grind)
    | exact resolve eq1744 eq13945
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1744 eq13945
  have eq13976 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq13965
  have eq14056 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13976
       grind)
    | exact superpose eq13976 eq16
    | exact resolve eq16 eq13976
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13976
  have eq14080 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq14056
       have i₂ := eq13510
       grind)
    | exact superpose eq13510 eq14056
    | exact resolve eq14056 eq13510
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13510 eq14056
  have eq14081 : False := by grind
  exact eq14081

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_y_pxx_pyy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq62 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X0) (M.op (M.op X0 X1) X2)) := by
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
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq69 (σ X0)
       grind)
    | exact superpose eq69 eq15
    | exact resolve eq15 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq72 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq72
    | exact resolve eq72 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq72
  have eq100 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq12
    | exact resolve eq12 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq981 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1006 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq981 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq981
  have eq1146 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1006 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006
  have eq1150 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1146 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq1146 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq1146 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq1146 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq1146 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1146
  have eq1207 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1150 (σ X1) (σ X0)
       grind)
    | exact superpose eq1150 eq15
    | (have j1 := eq1150 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1215 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq1150 (τ X1) X0
       grind)
    | exact superpose eq1150 eq17
    | (have j1 := eq1150 (τ X1) X0
       grind)
    | exact resolve eq17 eq1150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1150
  have eq1333 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1215 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1215
    | exact resolve eq1215 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1215
  have eq1408 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1333 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1333
    | (have j0 := eq1333 X0 X1
       grind)
    | exact resolve eq1333 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1333
  have eq1917 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1207 x y
       grind)
    | exact superpose eq1207 eq16
    | (have j1 := eq1207 x y
       grind)
    | exact resolve eq16 eq1207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1962 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1207 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1207
  have eq2195 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1917
       have i₂ := eq1408 y x
       grind)
    | exact superpose eq1408 eq1917
    | (have j1 := eq1408 (σ y) (σ x)
       grind)
    | (have r₁ := eq1917
       have r₂ := eq1408 y x
       grind)
    | exact resolve eq1917 eq1408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1917
  have eq2196 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2195
  have eq2200 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2196
       grind)
    | exact superpose eq2196 eq16
    | exact resolve eq16 eq2196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2202 : (σ x) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq100 y (σ x)
       have i₂ := eq2196
       grind)
    | exact superpose eq2196 eq100
    | (have j0 := eq100 y (σ x)
       grind)
    | exact resolve eq100 eq2196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq2204 : (σ x) ≠ (σ x) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2196
       grind)
    | exact superpose eq2196 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2196
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2196
       grind)
    | exact resolve eq13 eq2196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2206 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq63 (σ x) (σ y)
       have i₂ := eq2196
       grind)
    | exact superpose eq2196 eq63
    | exact resolve eq63 eq2196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2196
  have eq2209 : (k (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2204
  have eq2211 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2206
       have i₂ := eq83 x
       grind)
    | exact superpose eq83 eq2206
    | exact resolve eq2206 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2206
  have eq2213 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2209
       have i₂ := eq83 x
       grind)
    | exact superpose eq83 eq2209
    | exact resolve eq2209 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2209
  have eq2214 : (σ x) ≠ (σ (M.op y y)) ∨ (σ (k y x)) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2202
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2202
    | exact resolve eq2202 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2202
  have eq2216 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2213
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2213
    | exact resolve eq2213 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2213
  have eq2217 : (σ (k y x)) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2216
       have i₂ := eq83 y
       grind)
    | exact superpose eq83 eq2216
    | exact resolve eq2216 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2216
  have eq2225 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2211
       grind)
    | exact superpose eq2211 eq10
    | exact resolve eq10 eq2211
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2211
  have eq2273 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2225
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2225
    | exact resolve eq2225 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2225
  have eq2283 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq63 x y
       have i₂ := eq2273
       grind)
    | exact superpose eq2273 eq63
    | exact resolve eq63 eq2273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq2273
  have eq2286 : x = (M.op x x) := by grind
  clear eq2283
  have eq2375 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X3) X3) = (M.op (M.op (M.op (M.op (M.op (M.op X0 X1) X2) X2) X4) X4) (M.op (M.op X0 X3) X3)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op (M.op X0 X3) X3) (M.op (M.op (M.op X0 X1) X2) X2) X4
       have i₂ := eq61 X0 X1 X2 X3
       grind)
    | exact superpose eq61 eq9
    | exact resolve eq9 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq2408 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op x (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 x X0 X1
       have i₂ := eq2286
       grind)
    | exact superpose eq2286 eq62
    | exact resolve eq62 eq2286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq127202 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) X2) = (M.op (M.op X0 X1) (M.op (M.op X0 X2) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2375 X0 X1 (M.op X0 X1) X2 (M.op X0 X1)
       have i₂ := eq9 (M.op X0 X1) (M.op X0 X1) (M.op X0 X1)
       grind)
    | exact superpose eq9 eq2375
    | exact resolve eq2375 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2375
  have eq128132 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op (M.op X0 X1) X0) X2) X0) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq127202 (M.op (M.op X0 X1) X0) X1 X0
       have i₂ := eq9 X0 X1 X0
       grind)
    | exact superpose eq9 eq127202
    | exact resolve eq127202 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127202
  have eq550483 : (σ (M.op x y)) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1408 y x
       have i₂ := eq2217
       grind)
    | exact superpose eq2217 eq1408
    | (have j0 := eq1408 y x
       grind)
    | exact resolve eq1408 eq2217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2217
  have eq550654 : (σ (M.op x y)) = (σ (M.op x x)) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq550483
  have eq550765 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq550654
       have i₂ := eq2286
       grind)
    | exact superpose eq2286 eq550654
    | exact resolve eq550654 eq2286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550654
  have eq550826 : (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq550765
       have r₂ := eq2200
       grind)
    | exact resolve eq550765 eq2200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550765
  have eq550836 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2214
       have i₂ := eq550826
       grind)
    | exact superpose eq550826 eq2214
    | (have r₁ := eq2214
       have r₂ := eq550826
       grind)
    | exact resolve eq2214 eq550826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2214 eq550826
  have eq551015 : (σ x) ≠ (σ x) ∨ (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
  clear eq550836
  have eq551016 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by grind
  clear eq551015
  have eq551679 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1408 y x
       have i₂ := eq551016
       grind)
    | exact superpose eq551016 eq1408
    | (have j0 := eq1408 y x
       grind)
    | exact resolve eq1408 eq551016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1408 eq551016
  have eq551852 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by grind
  clear eq551679
  have eq551882 : x = (M.op x y) := by
    first
    | (have r₁ := eq551852
       have r₂ := eq2200
       grind)
    | exact resolve eq551852 eq2200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2200 eq551852
  have eq551995 : x ≠ x ∨ (k y x) = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq551882
       grind)
    | exact superpose eq551882 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq551882
       grind)
    | exact resolve eq13 eq551882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq552053 : (k y x) = (M.op x x) ∨ x = (M.op y y) := by grind
  clear eq551995
  have eq552074 : x = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq552053
       have i₂ := eq2286
       grind)
    | exact superpose eq2286 eq552053
    | exact resolve eq552053 eq2286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2286 eq552053
  have eq552317 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1962 x y
       have i₂ := eq552074
       grind)
    | exact superpose eq552074 eq1962
    | (have j0 := eq1962 x y
       grind)
    | exact resolve eq1962 eq552074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1962 eq552074
  have eq552461 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq552317
  have eq554135 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq552461
       grind)
    | exact superpose eq552461 eq16
    | exact resolve eq16 eq552461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552461
  have eq554314 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq554135
       have i₂ := eq551882
       grind)
    | exact superpose eq551882 eq554135
    | exact resolve eq554135 eq551882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554135
  have eq554315 : x = (M.op y y) := by grind
  clear eq554314
  have eq554576 : ∀ X0 : G, y = (M.op (M.op (M.op x y) X0) y) := by
    intro X0
    first
    | (have i₁ := eq128132 y y X0
       have i₂ := eq554315
       grind)
    | exact superpose eq554315 eq128132
    | exact resolve eq128132 eq554315
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq128132 eq554315
  have eq554631 : ∀ X0 : G, y = (M.op (M.op x X0) y) := by
    intro X0
    first
    | (have i₁ := eq554576 X0
       have i₂ := eq551882
       grind)
    | exact superpose eq551882 eq554576
    | exact resolve eq554576 eq551882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554576
  have eq555109 : y = (M.op x y) := by
    first
    | (have i₁ := eq2408 x y
       have i₂ := eq554631 x
       grind)
    | exact superpose eq554631 eq2408
    | exact resolve eq2408 eq554631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2408 eq554631
  have eq555320 : x = y := by
    first
    | (have i₁ := eq555109
       have i₂ := eq551882
       grind)
    | exact superpose eq551882 eq555109
    | exact resolve eq555109 eq551882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq551882 eq555109
  have eq555350 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq555320
       grind)
    | exact superpose eq555320 eq16
    | exact resolve eq16 eq555320
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555320
  have eq555392 : False := by grind
  exact eq555392

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_y_pxx_y_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
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
  have eq62 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X0) (M.op (M.op X0 X1) X2)) := by
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
  have eq69 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq69 (σ X0)
       grind)
    | exact superpose eq69 eq15
    | exact resolve eq15 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq72 X0
       have i₂ := eq69 X0
       grind)
    | exact superpose eq69 eq72
    | exact resolve eq72 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq72
  have eq99 : ∀ X0 X1 : G, (σ X0) = (M.op (M.op (M.op (σ (M.op X0 X0)) X1) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X0) X1
       have i₂ := eq83 X0
       grind)
    | exact superpose eq83 eq9
    | exact resolve eq9 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq142 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op (M.op X0 X0) (M.op X0 X0))) (σ (M.op X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq99 X0 (σ (M.op X0 X0))
       have i₂ := eq83 (M.op X0 X0)
       grind)
    | exact superpose eq83 eq99
    | exact resolve eq99 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq764 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq781 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq764 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764
  have eq1132 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq781 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq781
  have eq1136 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1132 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq1132 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq1132 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq1132 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | exact resolve eq1132 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1132
  have eq1193 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1136 (σ X1) (σ X0)
       grind)
    | exact superpose eq1136 eq15
    | (have j1 := eq1136 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1201 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X1 X0
       have i₂ := eq1136 (τ X1) X0
       grind)
    | exact superpose eq1136 eq17
    | (have j1 := eq1136 (τ X1) X0
       grind)
    | exact resolve eq17 eq1136
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq1136
  have eq1319 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1201 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1201
    | exact resolve eq1201 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1201
  have eq1394 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1319 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq1319
    | (have j0 := eq1319 X0 X1
       grind)
    | exact resolve eq1319 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1319
  have eq1903 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1193 x y
       grind)
    | exact superpose eq1193 eq16
    | (have j1 := eq1193 x y
       grind)
    | exact resolve eq16 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1948 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq1193 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193
  have eq2181 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1903
       have i₂ := eq1394 y x
       grind)
    | exact superpose eq1394 eq1903
    | (have j1 := eq1394 (σ y) (σ x)
       grind)
    | (have r₁ := eq1903
       have r₂ := eq1394 y x
       grind)
    | exact resolve eq1903 eq1394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903
  have eq2182 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2181
  have eq2186 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2182
       grind)
    | exact superpose eq2182 eq16
    | exact resolve eq16 eq2182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2190 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq2182
       grind)
    | exact superpose eq2182 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2182
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2182
       grind)
    | exact resolve eq13 eq2182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2192 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq63 (σ x) (σ y)
       have i₂ := eq2182
       grind)
    | exact superpose eq2182 eq63
    | exact resolve eq63 eq2182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2182
  have eq2195 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2190
  have eq2197 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2192
       have i₂ := eq83 x
       grind)
    | exact superpose eq83 eq2192
    | exact resolve eq2192 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2192
  have eq2199 : (σ x) = (σ (k y x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2195
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq2195
    | exact resolve eq2195 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2195
  have eq2202 : (σ x) = (σ (k y x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2199
       have i₂ := eq83 y
       grind)
    | exact superpose eq83 eq2199
    | exact resolve eq2199 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2199
  have eq2210 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq2197
       grind)
    | exact superpose eq2197 eq10
    | exact resolve eq10 eq2197
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2197
  have eq2258 : x = (M.op x y) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2210
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2210
    | exact resolve eq2210 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2210
  have eq2268 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq63 x y
       have i₂ := eq2258
       grind)
    | exact superpose eq2258 eq63
    | exact resolve eq63 eq2258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq2258
  have eq2271 : x = (M.op x x) := by grind
  clear eq2268
  have eq2393 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op x (M.op (M.op x X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 x X0 X1
       have i₂ := eq2271
       grind)
    | exact superpose eq2271 eq62
    | exact resolve eq62 eq2271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq2839 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x X0) X1) X2) = (M.op x (M.op (M.op (M.op x X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2393 (M.op (M.op x X0) X1) X1
       have i₂ := eq2393 X0 X1
       grind)
    | exact superpose eq2393 eq2393
    | exact resolve eq2393 eq2393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2393
  have eq15507 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1394 y x
       have i₂ := eq2202
       grind)
    | exact superpose eq2202 eq1394
    | (have j0 := eq1394 y x
       grind)
    | exact resolve eq1394 eq2202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394 eq2202
  have eq15550 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ (σ x) = (σ (M.op y y)) := by grind
  clear eq15507
  have eq15576 : (σ x) = (σ (M.op y y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq15550
       have r₂ := eq2186
       grind)
    | exact resolve eq15550 eq2186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2186 eq15550
  have eq15591 : (M.op y y) = (τ (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq15576
       grind)
    | exact superpose eq15576 eq10
    | exact resolve eq10 eq15576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15576
  have eq15650 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15591
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq15591
    | exact resolve eq15591 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15591
  have eq15664 : (σ y) = (M.op (M.op (σ (M.op x x)) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq142 y
       have i₂ := eq15650
       grind)
    | exact superpose eq15650 eq142
    | exact resolve eq142 eq15650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142
  have eq15691 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) X0) y) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq9 y y X0
       have i₂ := eq15650
       grind)
    | exact superpose eq15650 eq9
    | exact resolve eq9 eq15650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15650
  have eq15707 : (σ y) = (M.op (M.op (σ x) (σ x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15664
       have i₂ := eq2271
       grind)
    | exact superpose eq2271 eq15664
    | exact resolve eq15664 eq2271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15664
  have eq15709 : (σ y) = (M.op (σ (M.op x x)) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15707
       have i₂ := eq83 x
       grind)
    | exact superpose eq83 eq15707
    | exact resolve eq15707 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15707
  have eq15711 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq15709
       have i₂ := eq2271
       grind)
    | exact superpose eq2271 eq15709
    | exact resolve eq15709 eq2271
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2271 eq15709
  have eq16055 : (σ (M.op x y)) ≠ (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15711
       grind)
    | exact superpose eq15711 eq16
    | exact resolve eq16 eq15711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15711
  have eq16208 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2839 x x y
       have i₂ := eq15691 x
       grind)
    | exact superpose eq15691 eq2839
    | exact resolve eq2839 eq15691
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15691
  have eq16245 : (σ y) ≠ (σ y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16055
       have i₂ := eq16208
       grind)
    | exact superpose eq16208 eq16055
    | exact resolve eq16055 eq16208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16055
  have eq16301 : x ≠ y ∨ x = (M.op x y) := by grind
  clear eq16208
  have eq16302 : x = y ∨ x = (M.op x y) := by grind
  clear eq16245
  have eq16310 : x = (M.op x y) := by
    first
    | (have r₁ := eq16302
       have r₂ := eq16301
       grind)
    | exact resolve eq16302 eq16301
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16301 eq16302
  have eq16354 : x ≠ x ∨ x = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq16310
       grind)
    | exact superpose eq16310 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq16310
       grind)
    | exact resolve eq13 eq16310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16362 : x = (k y x) ∨ x = (M.op y y) := by grind
  clear eq16354
  have eq16401 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1948 x y
       have i₂ := eq16362
       grind)
    | exact superpose eq16362 eq1948
    | (have j0 := eq1948 x y
       grind)
    | exact resolve eq1948 eq16362
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1948 eq16362
  have eq16412 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq16401
  have eq16957 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16412
       grind)
    | exact superpose eq16412 eq16
    | exact resolve eq16 eq16412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16412
  have eq17020 : (σ x) ≠ (σ x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16957
       have i₂ := eq16310
       grind)
    | exact superpose eq16310 eq16957
    | exact resolve eq16957 eq16310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16957
  have eq17021 : x = (M.op y y) := by grind
  clear eq17020
  have eq17071 : ∀ X0 : G, y = (M.op (M.op (M.op x X0) X0) y) := by
    intro X0
    first
    | (have i₁ := eq9 y y X0
       have i₂ := eq17021
       grind)
    | exact superpose eq17021 eq9
    | exact resolve eq9 eq17021
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17021
  have eq17463 : y = (M.op x y) := by
    first
    | (have i₁ := eq2839 x x y
       have i₂ := eq17071 x
       grind)
    | exact superpose eq17071 eq2839
    | exact resolve eq2839 eq17071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2839 eq17071
  have eq17508 : x = y := by
    first
    | (have i₁ := eq17463
       have i₂ := eq16310
       grind)
    | exact superpose eq16310 eq17463
    | exact resolve eq17463 eq16310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16310 eq17463
  have eq17523 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq17508
       grind)
    | exact superpose eq17508 eq16
    | exact resolve eq16 eq17508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17508
  have eq17578 : False := by grind
  exact eq17578

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyx_pyy_pyx_pyy_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq55 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq54 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq54 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq54 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq54 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq59 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq56 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq56 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq56 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq114 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq57 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq57
    | (have j0 := eq57 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq57 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq57 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq57 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57
  have eq124 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq114 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq128 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq124 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq124 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq124 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq124 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq129 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq128 X0 X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq128
    | (have j0 := eq128 X0 X1
       grind)
    | exact resolve eq128 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq128
  have eq154 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq59 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq158 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq154 X0 X1
       have j1 := eq129 X1 X0
       grind)
    | (have r₁ := eq154 X1 X1
       have r₂ := eq129 X1 X1
       grind)
    | (have r₁ := eq154 X1 X0
       have r₂ := eq129 X0 X1
       grind)
    | exact resolve eq154 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq154
  have eq489 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq158 (σ X1) (σ X0)
       grind)
    | exact superpose eq158 eq15
    | exact resolve eq15 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq496 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq489 X0 X1
       have i₂ := eq158 X1 X0
       grind)
    | exact superpose eq158 eq489
    | exact resolve eq489 eq158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq489
  have eq499 : False := by grind
  exact eq499

/-- `Equation3093`: `x = (((x ◇ y) ◇ z) ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_x_y_pyx_pxx_pyx_Equation3093 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law3093 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3093.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq31 (σ X0)
       grind)
    | exact superpose eq31 eq15
    | exact resolve eq15 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq31 (τ X0)
       grind)
    | exact superpose eq31 eq18
    | exact resolve eq18 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq34
    | exact resolve eq34 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq36 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq33 X0
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq33
    | exact resolve eq33 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq38 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq35 X0
       have i₂ := eq31 X0
       grind)
    | exact superpose eq31 eq35
    | exact resolve eq35 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq35
  have eq51 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq54 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X1
       have i₂ := eq36 X1
       grind)
    | exact superpose eq36 eq51
    | (have j0 := eq51 X0 X1
       grind)
    | exact resolve eq51 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq56 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0 X1
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq54
    | (have j0 := eq54 X0 X1
       grind)
    | exact resolve eq54 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq77 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq56 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56
    | (have j0 := eq56 (τ X0) X1
       grind)
    | exact resolve eq56 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq197 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq183 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq183
    | (have j0 := eq183 X0 X1
       grind)
    | exact resolve eq183 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq203 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op X1 X1)) ∨ (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq197 X0 X1
       have i₂ := eq38 X0
       grind)
    | exact superpose eq38 eq197
    | (have j0 := eq197 X0 X1
       grind)
    | exact resolve eq197 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq197
  have eq207 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq203 X0 X1
       have j1 := eq77 X1 X0
       grind)
    | (have r₁ := eq203 X1 X0
       have r₂ := eq77 X0 X1
       grind)
    | (have r₁ := eq203 (M.op X1 X1) (M.op X0 X0)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq203 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq203
  have eq254 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq207 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq207
    | exact resolve eq207 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq207 (σ X1) X0
       grind)
    | exact superpose eq207 eq15
    | (have j1 := eq207 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207
  have eq268 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq254 X0 (τ X1)
       grind)
    | exact superpose eq254 eq18
    | (have j1 := eq254 (k X1 (σ X0)) (σ (M.op X0 (τ X1)))
       grind)
    | exact resolve eq18 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq254
  have eq530 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq268 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq268
    | exact resolve eq268 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq569 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq530 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq530
    | (have j0 := eq530 (σ (k X0 X1)) (σ (M.op X1 X0))
       grind)
    | exact resolve eq530 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530
  have eq1135 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq259 x y
       grind)
    | exact superpose eq259 eq16
    | (have j1 := eq259 x y
       grind)
    | exact resolve eq16 eq259
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq1161 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1135
       have i₂ := eq569 y x
       grind)
    | exact superpose eq569 eq1135
    | (have j1 := eq569 (σ x) (σ y)
       grind)
    | (have r₁ := eq1135
       have r₂ := eq569 y x
       grind)
    | (have r₁ := eq1135
       have r₂ := eq569 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1135
       have r₂ := eq569 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1135 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569 eq1135
  have eq1162 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq1161
  have eq1227 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1162
       grind)
    | exact superpose eq1162 eq10
    | exact resolve eq10 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162
  have eq1272 : x = y ∨ x = y := by
    first
    | (have i₁ := eq1227
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1227
    | exact resolve eq1227 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq1273 : x = y := by grind
  clear eq1272
  have eq1275 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1273
       grind)
    | exact superpose eq1273 eq16
    | exact resolve eq16 eq1273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273
  have eq1276 : False := by grind
  exact eq1276
