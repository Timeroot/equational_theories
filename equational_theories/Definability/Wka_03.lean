import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4175`: `x ◇ y = ((y ◇ z) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_x_pxy_Equation4175 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4175 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4175.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X1 X2) X0) X1) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq26 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X1 X2)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op X1 X2) X0
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq83 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq69 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69
  have eq103 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq83 X0 (τ X1)
       grind)
    | exact superpose eq83 eq20
    | (have j1 := eq83 X0 (τ X1)
       grind)
    | exact resolve eq20 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq105 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq83 (σ X0) (σ X1)
       grind)
    | exact superpose eq83 eq15
    | (have j1 := eq83 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq113 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (k X1 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  clear eq83
  have eq1262 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq113 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq1263 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1262 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1262
  have eq1549 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1263 (σ X0)
       grind)
    | exact superpose eq1263 eq15
    | exact resolve eq15 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1556 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1549 X0
       have i₂ := eq1263 X0
       grind)
    | exact superpose eq1263 eq1549
    | exact resolve eq1549 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263 eq1549
  have eq2110 : ∀ X0 X1 : G, (M.op X1 (σ X0)) = (M.op (M.op (σ (M.op X0 X0)) X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (σ X0) (σ X0)
       have i₂ := eq1556 X0
       grind)
    | exact superpose eq1556 eq9
    | exact resolve eq9 eq1556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2127 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    grind
  have eq2159 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq2127 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq2127
    | exact resolve eq2127 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2127
  have eq2170 : ∀ X0 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq2159
  have eq3017 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq2110 X0 (σ X0)
       have i₂ := eq2170 X0
       grind)
    | exact superpose eq2170 eq2110
    | exact resolve eq2110 eq2170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2170
  have eq3038 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ (M.op (M.op X0 X0) X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq3017 X0
       have i₂ := eq1556 X0
       grind)
    | exact superpose eq1556 eq3017
    | exact resolve eq3017 eq1556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3017
  have eq3388 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq103 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq103
    | exact resolve eq103 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103
  have eq3555 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq3388 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3388
    | (have j0 := eq3388 X0 X1
       grind)
    | exact resolve eq3388 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3388
  have eq6518 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq105 X0 X1
       grind)
    | exact superpose eq105 eq10
    | (have j1 := eq105 X0 X1
       grind)
    | exact resolve eq10 eq105
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq6696 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6518 X0 X1
       have i₂ := eq1556 X0
       grind)
    | exact superpose eq1556 eq6518
    | (have j0 := eq6518 X0 X1
       grind)
    | exact resolve eq6518 eq1556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6518
  have eq6821 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq6696 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq6696
    | (have j0 := eq6696 X0 X1
       grind)
    | exact resolve eq6696 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6696
  have eq7507 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6821 x y
       grind)
    | exact superpose eq6821 eq16
    | (have j1 := eq6821 x y
       grind)
    | exact resolve eq16 eq6821
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6821
  have eq7598 : y = (M.op x x) := by
    first
    | (have j1 := eq3555 y x
       grind)
    | (have r₁ := eq7507
       have r₂ := eq3555 y x
       grind)
    | exact resolve eq7507 eq3555
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3555 eq7507
  have eq8019 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op (M.op (σ y) X0) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq2110 x X0
       have i₂ := eq7598
       grind)
    | exact superpose eq7598 eq2110
    | exact resolve eq2110 eq7598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2110
  have eq8022 : (σ y) = (M.op (σ (M.op y x)) (σ x)) := by
    first
    | (have i₁ := eq3038 x
       have i₂ := eq7598
       grind)
    | exact superpose eq7598 eq3038
    | exact resolve eq3038 eq7598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3038
  have eq8027 : ∀ X0 : G, (M.op x y) = (M.op (M.op X0 x) y) := by
    intro X0
    first
    | (have i₁ := eq26 X0 x x
       have i₂ := eq7598
       grind)
    | exact superpose eq7598 eq26
    | exact resolve eq26 eq7598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq9685 : (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq8027 x
       have i₂ := eq7598
       grind)
    | exact superpose eq7598 eq8027
    | exact resolve eq8027 eq7598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7598 eq8027
  have eq16368 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op X0 (σ x)) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq9 (σ x) (σ y) X0
       have i₂ := eq8019 X0
       grind)
    | exact superpose eq8019 eq9
    | exact resolve eq9 eq8019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8019
  have eq33855 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16368 (σ (M.op y x))
       have i₂ := eq8022
       grind)
    | exact superpose eq8022 eq16368
    | exact resolve eq16368 eq8022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8022 eq16368
  have eq33972 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq33855
       have i₂ := eq1556 y
       grind)
    | exact superpose eq1556 eq33855
    | exact resolve eq33855 eq1556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1556 eq33855
  have eq33982 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq33972
       have i₂ := eq9685
       grind)
    | exact superpose eq9685 eq33972
    | exact resolve eq33972 eq9685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9685 eq33972
  have eq33989 : False := by grind
  exact eq33989

/-- `Equation4192`: `x ◇ y = ((z ◇ x) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_y_pxy_pxx_pxy_Equation4192 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4192 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4192.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X0) X0) X1) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq25 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op x X0)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 (M.op X0 X0)) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (M.op X0 X0)
       have i₂ := eq25 X0 X1
       grind)
    | exact superpose eq25 eq12
    | (have j0 := eq12 X1 X0
       grind)
    | exact resolve eq12 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq500 : ∀ X0 X1 : G, (σ X1) = X0 ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X1 X1
       have i₂ := eq14 (σ X1) X1
       grind)
    | (have i₁ := eq60 X0 X1
       have i₂ := eq14 X0 (M.op (σ X1) (σ X0))
       grind)
    | exact superpose eq14 eq60
    | (have j1 := eq14 (σ X1) X0
       grind)
    | exact resolve eq60 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq538 : ∀ X0 X1 : G, (σ X0) ≠ (σ X0) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq60 X0 X1
       grind)
    | exact superpose eq60 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq60 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq60 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq60 X0 X1
       grind)
    | exact resolve eq12 eq60
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq552 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq538 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq538
  have eq559 : ∀ X0 X1 : G, (σ X1) = X0 ∨ (σ (k X1 X1)) = X0 ∨ (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ X1) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq500 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq500
  have eq565 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq552 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq552
    | (have j0 := eq552 X0 X1
       grind)
    | exact resolve eq552 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq552
  have eq566 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq565 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq565
  have eq580 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (k X1 X1)) = X0 ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq559 X0 X1
       have j1 := eq12 (σ X1) X0
       grind)
    | (have r₁ := eq559 (M.op X1 (σ X1)) X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | (have r₁ := eq559 (M.op X1 (σ (k X1 X1))) X1
       have r₂ := eq12 (σ (k X1 X1)) X1
       grind)
    | (have r₁ := eq559 X1 X1
       have r₂ := eq12 (σ X1) X1
       grind)
    | exact resolve eq559 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq559
  have eq995 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq33 X0 X1
       have i₂ := eq14 X0 (M.op X0 X1)
       grind)
    | exact superpose eq14 eq33
    | (have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq33 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq33 X0 (M.op X0 X0)
       have r₂ := eq14 X0 (M.op X0 (M.op X0 X0))
       grind)
    | (have r₁ := eq33 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq33 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq1003 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq995 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq1006 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq1003 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq1003 (M.op X0 X1) (k X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq1003 (k X0 X1) (M.op X0 X1)
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq1003 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq1003 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1003
  have eq1162 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1006 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1216 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq1162 (σ X0)
       grind)
    | exact superpose eq1162 eq15
    | exact resolve eq15 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1227 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq1216 X0
       have i₂ := eq1162 X0
       grind)
    | exact superpose eq1162 eq1216
    | exact resolve eq1216 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1216
  have eq1455 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq25 (σ X0) X1
       have i₂ := eq1227 X0
       grind)
    | exact superpose eq1227 eq25
    | exact resolve eq25 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1561 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq566 X0 X1
       grind)
    | exact superpose eq566 eq10
    | (have j1 := eq566 X0 X1
       grind)
    | exact resolve eq10 eq566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566
  have eq1652 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1561 X0 X1
       have i₂ := eq1227 X0
       grind)
    | exact superpose eq1227 eq1561
    | (have j0 := eq1561 X0 X1
       grind)
    | exact resolve eq1561 eq1227
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1561
  have eq1723 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1652 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq1652
    | (have j0 := eq1652 X0 X1
       grind)
    | exact resolve eq1652 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1652
  have eq2191 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq1227 (M.op X0 X0)
       have i₂ := eq1455 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq1455 eq1227
    | exact resolve eq1227 eq1455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227 eq1455
  have eq2244 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2191 X0
       have i₂ := eq25 X0 (M.op X0 X0)
       grind)
    | exact superpose eq25 eq2191
    | exact resolve eq2191 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq2191
  have eq2356 : ∀ X0 X1 : G, (k (σ (τ X1)) X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) ∨ (σ (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 (τ X1)
       have i₂ := eq580 X0 (τ X1)
       grind)
    | (have i₁ := eq19 X0 X1
       have i₂ := eq580 (σ (k X1 (τ X0))) X1
       grind)
    | exact superpose eq580 eq19
    | (have j1 := eq580 X0 (τ X1)
       grind)
    | exact resolve eq19 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq580
  have eq2414 : ∀ X0 X1 : G, (k (σ (τ X1)) X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have j0 := eq2356 X0 X1
       have j1 := eq1006 X0 (σ (τ X1))
       grind)
    | (have r₁ := eq2356 X1 X1
       have r₂ := eq1006 (k (σ (τ X1)) X1) X1
       grind)
    | (have r₁ := eq2356 X0 X1
       have r₂ := eq1006 X0 (k (σ (τ X1)) X1)
       grind)
    | (have r₁ := eq2356 X0 X1
       have r₂ := eq1006 (k (σ (τ X1)) X0) (M.op (σ (τ X1)) X0)
       grind)
    | exact resolve eq2356 eq1006
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1006 eq2356
  have eq2472 : ∀ X0 X1 : G, (k X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2414 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq2414
    | (have j0 := eq2414 X0 X1
       grind)
    | exact resolve eq2414 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2414
  have eq2502 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ (τ X1)) X0) = (M.op (σ (τ X1)) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2472 X0 X1
       have i₂ := eq1162 X1
       grind)
    | exact superpose eq1162 eq2472
    | (have j0 := eq2472 X0 X1
       grind)
    | exact resolve eq2472 eq1162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1162 eq2472
  have eq2515 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq2502 X0 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq2502
    | (have j0 := eq2502 X0 X1
       grind)
    | exact resolve eq2502 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2502
  have eq16526 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1723 x y
       grind)
    | exact superpose eq1723 eq16
    | (have j1 := eq1723 x y
       grind)
    | exact resolve eq16 eq1723
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1723
  have eq17102 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16526
       have i₂ := eq2515 y x
       grind)
    | exact superpose eq2515 eq16526
    | (have j1 := eq2515 y x
       grind)
    | exact resolve eq16526 eq2515
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2515 eq16526
  have eq17107 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op x x) := by grind
  clear eq17102
  have eq17108 : y = (M.op x x) := by grind
  clear eq17107
  have eq17262 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2244 x
       have i₂ := eq17108
       grind)
    | exact superpose eq17108 eq2244
    | exact resolve eq2244 eq17108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2244 eq17108
  have eq17306 : False := by grind
  exact eq17306

/-- `Equation4192`: `x ◇ y = ((z ◇ x) ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pxy_x_pxy_Equation4192 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4192 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4192.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op (M.op X2 X0) X0) X1) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq26 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0 X1 (M.op x X0)
       have i₂ := eq9 X0 X0 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq97 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq80 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq125 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq97 X0 (τ X1)
       grind)
    | exact superpose eq97 eq20
    | (have j1 := eq97 X0 (τ X1)
       grind)
    | exact resolve eq20 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq127 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq97 (σ X0) (σ X1)
       grind)
    | exact superpose eq97 eq15
    | (have j1 := eq97 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  clear eq97
  have eq2152 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq134 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq2153 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq2152 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2152
  have eq2171 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq2153 (σ X0)
       grind)
    | exact superpose eq2153 eq15
    | exact resolve eq15 eq2153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2178 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2171 X0
       have i₂ := eq2153 X0
       grind)
    | exact superpose eq2153 eq2171
    | exact resolve eq2171 eq2153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2153 eq2171
  have eq2747 : ∀ X0 X1 : G, (M.op (σ X0) X1) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq26 (σ X0) X1
       have i₂ := eq2178 X0
       grind)
    | exact superpose eq2178 eq26
    | exact resolve eq26 eq2178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3194 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq2178 (M.op X0 X0)
       have i₂ := eq2747 X0 (σ (M.op X0 X0))
       grind)
    | exact superpose eq2747 eq2178
    | exact resolve eq2178 eq2747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2747
  have eq3275 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq3194 X0
       have i₂ := eq26 X0 (M.op X0 X0)
       grind)
    | exact superpose eq26 eq3194
    | exact resolve eq3194 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq3194
  have eq4586 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq125 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq125
    | exact resolve eq125 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq4758 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4586 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq4586
    | (have j0 := eq4586 X0 X1
       grind)
    | exact resolve eq4586 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4586
  have eq7059 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq127 X0 X1
       grind)
    | exact superpose eq127 eq10
    | (have j1 := eq127 X0 X1
       grind)
    | exact resolve eq10 eq127
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq7225 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7059 X0 X1
       have i₂ := eq2178 X0
       grind)
    | exact superpose eq2178 eq7059
    | (have j0 := eq7059 X0 X1
       grind)
    | exact resolve eq7059 eq2178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2178 eq7059
  have eq7344 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq7225 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq7225
    | (have j0 := eq7225 X0 X1
       grind)
    | exact resolve eq7225 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7225
  have eq18192 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq7344 x y
       grind)
    | exact superpose eq7344 eq16
    | (have j1 := eq7344 x y
       grind)
    | exact resolve eq16 eq7344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7344
  have eq18329 : y = (M.op x x) := by
    first
    | (have j1 := eq4758 y x
       grind)
    | (have r₁ := eq18192
       have r₂ := eq4758 y x
       grind)
    | exact resolve eq18192 eq4758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4758 eq18192
  have eq19069 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq3275 x
       have i₂ := eq18329
       grind)
    | exact superpose eq18329 eq3275
    | exact resolve eq3275 eq18329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3275 eq18329
  have eq19098 : False := by grind
  exact eq19098

/-- `Equation4380`: `x ◇ (x ◇ x) = (x ◇ x) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(Y,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pyy_x_pyx_pyx_pxy_Equation4380 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4380 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4380.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op b b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (M.op (M.op X0 X0) X0) := by
    intro X0
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
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
  have eq39 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
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
  have eq48 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq49 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) (τ X0)) ∨ (τ X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq51 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X1 X2) = (M.op X2 X1) ∨ (k X2 X0) = (M.op X2 X0) ∨ (M.op X0 X0) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq14 X2 X0
       grind)
    | (have i₁ := eq12 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq14 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X2 X2) ∨ (k X1 X2) = (M.op X2 X1) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X2
       have i₂ := eq14 X1 X0
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X0 X2
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X0
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X1 X1
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq48 X0 X1
       have i₂ := eq39 X1
       grind)
    | exact superpose eq39 eq48
    | (have j0 := eq48 X0 X1
       grind)
    | exact resolve eq48 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq60 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 X0 X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq58
    | (have j0 := eq58 X0 X1
       grind)
    | exact resolve eq58 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq62 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X1
       have i₂ := eq39 X1
       grind)
    | exact superpose eq39 eq60
    | (have j0 := eq60 X0 X1
       grind)
    | exact resolve eq60 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq64 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq87 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 (M.op X0 X0)) = (k (M.op X0 X0) X1) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0 X1
    grind
  have eq121 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq308 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq361 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq52 X1 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq550 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq62 x y
       grind)
    | exact superpose eq62 eq16
    | (have j1 := eq62 x y
       grind)
    | exact resolve eq16 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (σ (M.op X0 X0))) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq62 X0 X1
       grind)
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq62 X0 X1
       grind)
    | exact superpose eq62 eq10
    | (have j1 := eq62 X0 X1
       grind)
    | exact resolve eq10 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62
  have eq599 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq568 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq568
    | (have j0 := eq568 X0 X1
       grind)
    | exact resolve eq568 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568
  have eq797 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) ∨ (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq87 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq798 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have j0 := eq797 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq808 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (k (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq798 (σ X0)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq798
    | exact resolve eq798 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq827 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq808 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq808
    | exact resolve eq808 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq808
  have eq837 : ∀ X0 : G, (M.op (σ X0) (σ (M.op X0 X0))) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq827 X0
       have i₂ := eq798 X0
       grind)
    | exact superpose eq798 eq827
    | exact resolve eq827 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827
  have eq2858 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq121 X1 (σ X0)
       have i₂ := eq39 X0
       grind)
    | exact superpose eq39 eq121
    | (have j0 := eq121 X1 (σ X0)
       grind)
    | (have r₁ := eq121 X0 (σ X0)
       have r₂ := eq39 X0
       grind)
    | exact resolve eq121 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq121
  have eq2889 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2858 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq2858
    | (have j0 := eq2858 X0 X1
       grind)
    | exact resolve eq2858 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2858
  have eq3350 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X0
       have i₂ := eq308 X0 X1
       grind)
    | (have i₁ := eq9 X0
       have i₂ := eq308 X0 (M.op X0 X0)
       grind)
    | exact superpose eq308 eq9
    | (have j1 := eq308 X1 X0
       grind)
    | exact resolve eq9 eq308
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq308
  have eq3693 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq798 X1
       have i₂ := eq361 X0 X1
       grind)
    | (have i₁ := eq798 X0
       have i₂ := eq361 (M.op X0 X0) X1
       grind)
    | exact superpose eq361 eq798
    | (have j1 := eq361 X0 X1
       grind)
    | exact resolve eq798 eq361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq361
  have eq3703 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3693 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3693
  have eq3823 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq3703 X0 (τ X1)
       grind)
    | exact superpose eq3703 eq19
    | (have j1 := eq3703 X0 (τ X1)
       grind)
    | exact resolve eq19 eq3703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq3845 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq3703 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3846 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq3703 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3938 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) ≠ (M.op X0 (M.op X0 X0)) ∨ (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq3845 X0 (M.op X0 X0)
       have i₂ := eq9 X0
       grind)
    | exact superpose eq9 eq3845
    | (have j0 := eq3845 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq3845 (M.op X0 X0) X0
       have r₂ := eq9 X0
       grind)
    | (have r₁ := eq3845 X0 (M.op X0 X0)
       have r₂ := eq9 X0
       grind)
    | exact resolve eq3845 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4080 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq3938 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3938
  have eq4556 : ∀ X0 X1 : G, (τ (σ X0)) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq599 X0 X1
       grind)
    | (have i₁ := eq10 X0
       have i₂ := eq599 X0 X1
       grind)
    | exact superpose eq599 eq10
    | (have j1 := eq599 X0 X1
       grind)
    | exact resolve eq10 eq599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq4599 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4556 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4556
    | (have j0 := eq4556 X0 X1
       grind)
    | exact resolve eq4556 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4556
  have eq4938 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq49 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq49
    | exact resolve eq49 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq5295 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq4938 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4938
    | (have j0 := eq4938 X0 X1
       grind)
    | exact resolve eq4938 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4938
  have eq11077 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq3823 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq3823
    | exact resolve eq3823 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3823
  have eq11234 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq11077 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq11077
    | (have j0 := eq11077 X0 X1
       grind)
    | exact resolve eq11077 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11077
  have eq11642 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq550
       have i₂ := eq11234 y x
       grind)
    | exact superpose eq11234 eq550
    | (have j1 := eq11234 y x
       grind)
    | (have r₁ := eq550
       have r₂ := eq11234 y x
       grind)
    | exact resolve eq550 eq11234
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq550 eq11234
  have eq11678 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (σ x) = (σ (M.op y y)) ∨ (k x y) = (M.op y x) := by grind
  clear eq11642
  have eq90590 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq3350 (σ X0) (σ X1)
       grind)
    | exact superpose eq3350 eq15
    | (have j1 := eq3350 (σ X0) (σ X1)
       grind)
    | exact resolve eq15 eq3350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90597 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) ∨ (M.op (τ X0) (τ X1)) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1
       have i₂ := eq3350 (τ X0) (τ X1)
       grind)
    | exact superpose eq3350 eq64
    | (have j1 := eq3350 (τ X0) (τ X1)
       grind)
    | exact resolve eq64 eq3350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3350
  have eq90612 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (k (τ X0) (τ X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq90597 X0 X1
       have j1 := eq3845 (τ X0) (τ X1)
       grind)
    | (have r₁ := eq90597 X0 X1
       have r₂ := eq3845 (τ X1) (τ X0)
       grind)
    | (have r₁ := eq90597 X0 X1
       have r₂ := eq3845 (τ X0) (τ X1)
       grind)
    | exact resolve eq90597 eq3845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90597
  have eq90619 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq90590 X0 X1
       have j1 := eq3845 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq90590 X0 X1
       have r₂ := eq3845 (σ X1) (σ X0)
       grind)
    | (have r₁ := eq90590 X0 X1
       have r₂ := eq3845 (σ X0) (σ X1)
       grind)
    | exact resolve eq90590 eq3845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90590
  have eq90650 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90612 X0 X1
       have i₂ := eq64 X1 X0
       grind)
    | exact superpose eq64 eq90612
    | (have j0 := eq90612 X0 X1
       grind)
    | exact resolve eq90612 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq90612
  have eq90651 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq90619 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq90619
    | (have j0 := eq90619 X0 X1
       grind)
    | exact resolve eq90619 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90619
  have eq104551 : ∀ X0 X1 : G, (τ (k X1 X0)) ≠ (τ (k X0 X1)) ∨ (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq90650 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104552 : ∀ X0 X1 : G, (τ (k X1 X0)) ≠ (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq90650 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90650
  have eq104977 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (k (σ X1) (σ X0))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq104551 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq104551
    | exact resolve eq104551 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104551
  have eq105054 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (k (τ (σ X1)) X0) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq104977 X0 X1
       have i₂ := eq23 (σ X1) X0
       grind)
    | exact superpose eq23 eq104977
    | (have j0 := eq104977 X0 X1
       grind)
    | exact resolve eq104977 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104977
  have eq105070 : ∀ X0 X1 : G, (k X1 X0) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq105054 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq105054
    | (have j0 := eq105054 X0 X1
       grind)
    | exact resolve eq105054 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105054
  have eq105078 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq105070 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq105070
    | (have j0 := eq105070 X0 X1
       grind)
    | (have r₁ := eq105070 X1 X1
       have r₂ := eq10 (k X1 X1)
       grind)
    | exact resolve eq105070 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105070
  have eq105080 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq105078 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq105078
    | (have j0 := eq105078 X0 X1
       grind)
    | exact resolve eq105078 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105078
  have eq105082 : ∀ X0 X1 : G, (M.op X1 X0) = (τ (σ (k X0 X1))) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq105080 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq105080
    | (have j0 := eq105080 X0 X1
       grind)
    | exact resolve eq105080 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105080
  have eq105084 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq105082 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq105082
    | (have j0 := eq105082 X0 X1
       grind)
    | exact resolve eq105082 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105082
  have eq105752 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq105084 X0 X1
       have i₂ := eq3703 X0 X1
       grind)
    | exact superpose eq3703 eq105084
    | (have j0 := eq105084 X0 X1
       have j1 := eq3703 X0 X1
       grind)
    | exact resolve eq105084 eq3703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105763 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (k (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq105084 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq105084
    | exact resolve eq105084 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105849 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ (k X1 X0)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq105763 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq105763
    | (have j0 := eq105763 X0 X1
       grind)
    | (have r₁ := eq105763 X0 X0
       have r₂ := eq15 X0 X0
       grind)
    | exact resolve eq105763 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105763
  have eq105850 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq105752 X0 X1
       have j1 := eq3846 X0 X1
       grind)
    | (have r₁ := eq105752 X1 X0
       have r₂ := eq3846 X0 X1
       grind)
    | (have r₁ := eq105752 X0 X1
       have r₂ := eq3846 X0 X1
       grind)
    | exact resolve eq105752 eq3846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3846 eq105752
  have eq110726 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (k (σ X1) (σ X0))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq104552 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq104552
    | exact resolve eq104552 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104552
  have eq110755 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (k (τ (σ X1)) X0) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq110726 X0 X1
       have i₂ := eq23 (σ X1) X0
       grind)
    | exact superpose eq23 eq110726
    | (have j0 := eq110726 X0 X1
       grind)
    | exact resolve eq110726 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110726
  have eq110772 : ∀ X0 X1 : G, (k X1 X0) ≠ (τ (σ (k X0 X1))) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq110755 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq110755
    | (have j0 := eq110755 X0 X1
       grind)
    | exact resolve eq110755 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110755
  have eq110782 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) (τ (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq110772 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq110772
    | (have j0 := eq110772 X0 X1
       grind)
    | (have r₁ := eq110772 X1 X1
       have r₂ := eq10 (k X1 X1)
       grind)
    | exact resolve eq110772 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110772
  have eq110790 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) = (M.op (τ (σ X0)) X1) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq110782 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq110782
    | (have j0 := eq110782 X0 X1
       grind)
    | exact resolve eq110782 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110782
  have eq110792 : ∀ X0 X1 : G, (M.op X0 X1) = (τ (σ (k X0 X1))) ∨ (k X0 X1) ≠ (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq110790 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq110790
    | (have j0 := eq110790 X0 X1
       grind)
    | exact resolve eq110790 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110790
  have eq110794 : ∀ X0 X1 : G, (k X0 X1) ≠ (k X1 X0) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq110792 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq110792
    | (have j0 := eq110792 X0 X1
       grind)
    | exact resolve eq110792 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110792
  have eq110938 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq110794 X0 X1
       have i₂ := eq3703 X0 X1
       grind)
    | exact superpose eq3703 eq110794
    | (have j0 := eq110794 X1 X0
       have j1 := eq3703 X1 X0
       grind)
    | exact resolve eq110794 eq3703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3703 eq110794
  have eq111036 : ∀ X0 X1 : G, (k X0 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq110938 X0 X1
       have j1 := eq3845 X1 X0
       grind)
    | (have r₁ := eq110938 X0 X1
       have r₂ := eq3845 X0 X1
       grind)
    | (have r₁ := eq110938 X1 X0
       have r₂ := eq3845 X0 X1
       grind)
    | exact resolve eq110938 eq3845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3845 eq110938
  have eq111210 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq111036 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq111036
    | (have j0 := eq111036 (σ X0) (σ X1)
       grind)
    | exact resolve eq111036 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111036
  have eq111249 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq111210 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq111210
    | (have j0 := eq111210 X0 X1
       grind)
    | exact resolve eq111210 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111210
  have eq119002 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq90651 x y
       grind)
    | exact superpose eq90651 eq16
    | (have j1 := eq90651 x y
       grind)
    | exact resolve eq16 eq90651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90651
  have eq203147 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op x x) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq4599 x y
       grind)
    | exact superpose eq4599 eq16
    | (have j1 := eq4599 x y
       grind)
    | exact resolve eq16 eq4599
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4599
  have eq203207 : (M.op x x) = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have j1 := eq5295 x y
       grind)
    | (have r₁ := eq203147
       have r₂ := eq5295 x y
       grind)
    | exact resolve eq203147 eq5295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5295 eq203147
  have eq207230 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq203207
       grind)
    | exact superpose eq203207 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq203207
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq203207
       grind)
    | exact resolve eq12 eq203207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq207271 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k X0 y)) = (M.op (σ y) (σ X0)) ∨ x = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq2889 y X0
       have i₂ := eq203207
       grind)
    | exact superpose eq203207 eq2889
    | (have j0 := eq2889 X0 x
       grind)
    | exact resolve eq2889 eq203207
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2889 eq203207
  have eq231964 : (M.op x y) = (k y x) ∨ x = (M.op y y) := by
    first
    | (have j0 := eq207230 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207230
  have eq235149 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq105849 y x
       have i₂ := eq231964
       grind)
    | exact superpose eq231964 eq105849
    | exact resolve eq105849 eq231964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231964
  have eq235171 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq235149
       have r₂ := eq16
       grind)
    | exact resolve eq235149 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235149
  have eq2078750 : (M.op y y) = (τ (σ (M.op x x))) ∨ (σ x) = (σ (M.op y y)) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq11678
       grind)
    | exact superpose eq11678 eq10
    | exact resolve eq10 eq11678
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11678
  have eq2078752 : (M.op x x) = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq2078750
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq2078750
    | exact resolve eq2078750 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078750
  have eq2078753 : (σ x) = (σ (M.op y y)) ∨ (k x y) = (M.op y x) := by
    first
    | (have j1 := eq12 x y
       grind)
    | (have r₁ := eq2078752
       have r₂ := eq12 x y
       grind)
    | (have r₁ := eq2078752
       have r₂ := eq12 y x
       grind)
    | exact resolve eq2078752 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078752
  have eq2078794 : ∀ X0 : G, (k (τ X0) (M.op y y)) = (τ (k X0 (σ x))) ∨ (k x y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq23 X0 (M.op y y)
       have i₂ := eq2078753
       grind)
    | exact superpose eq2078753 eq23
    | exact resolve eq23 eq2078753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2078799 : ∀ X0 : G, (k (M.op y y) (τ X0)) = (τ (k (σ x) X0)) ∨ (k x y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq29 (M.op y y) X0
       have i₂ := eq2078753
       grind)
    | exact superpose eq2078753 eq29
    | exact resolve eq29 eq2078753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078753
  have eq2078810 : ∀ X0 : G, (k x (τ X0)) = (k (M.op y y) (τ X0)) ∨ (k x y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2078799 X0
       have i₂ := eq29 x X0
       grind)
    | exact superpose eq29 eq2078799
    | exact resolve eq2078799 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2078799
  have eq2078815 : ∀ X0 : G, (k (τ X0) x) = (k (τ X0) (M.op y y)) ∨ (k x y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2078794 X0
       have i₂ := eq23 X0 x
       grind)
    | exact superpose eq23 eq2078794
    | exact resolve eq2078794 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq2078794
  have eq2078834 : ∀ X0 : G, (k x X0) = (k (M.op y y) X0) ∨ (k x y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2078810 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2078810
    | exact resolve eq2078810 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078810
  have eq2078848 : (k x y) = (M.op y (M.op y y)) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq798 y
       have i₂ := eq2078834 y
       grind)
    | exact superpose eq2078834 eq798
    | exact resolve eq798 eq2078834
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798 eq2078834
  have eq2078892 : ∀ X0 : G, (k X0 x) = (k X0 (M.op y y)) ∨ (k x y) = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq2078815 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2078815
    | exact resolve eq2078815 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078815
  have eq2078918 : (k y x) = (M.op y (M.op y y)) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq4080 y
       have i₂ := eq2078892 y
       grind)
    | exact superpose eq2078892 eq4080
    | exact resolve eq4080 eq2078892
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4080 eq2078892
  have eq2078946 : (k x y) = (k y x) ∨ (k x y) = (M.op y x) ∨ (k x y) = (M.op y x) := by
    first
    | (have i₁ := eq2078848
       have i₂ := eq2078918
       grind)
    | exact superpose eq2078918 eq2078848
    | exact resolve eq2078848 eq2078918
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078848 eq2078918
  have eq2078947 : (k x y) = (k y x) ∨ (k x y) = (M.op y x) := by grind
  clear eq2078946
  have eq2078949 : (k x y) = (M.op y x) := by
    first
    | (have j1 := eq105084 x y
       grind)
    | (have r₁ := eq2078947
       have r₂ := eq105084 x y
       grind)
    | (have r₁ := eq2078947
       have r₂ := eq105084 y x
       grind)
    | exact resolve eq2078947 eq105084
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105084 eq2078947
  have eq2078990 : (M.op y x) ≠ (M.op y x) ∨ (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq105850 y x
       have i₂ := eq2078949
       grind)
    | exact superpose eq2078949 eq105850
    | (have j0 := eq105850 y x
       grind)
    | (have r₁ := eq105850 y x
       have r₂ := eq2078949
       grind)
    | exact resolve eq105850 eq2078949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105850
  have eq2079018 : (M.op x y) = (k y x) := by grind
  clear eq2078990
  have eq2079038 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (k x y)) := by
    first
    | (have i₁ := eq119002
       have i₂ := eq2079018
       grind)
    | exact superpose eq2079018 eq119002
    | exact resolve eq119002 eq2079018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119002
  have eq2079069 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq105849 y x
       have i₂ := eq2079018
       grind)
    | exact superpose eq2079018 eq105849
    | exact resolve eq105849 eq2079018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105849
  have eq2079105 : (M.op (σ x) (σ y)) = (σ (k x y)) := by grind
  clear eq2079038
  have eq2079112 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have r₁ := eq2079069
       have r₂ := eq16
       grind)
    | exact resolve eq2079069 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079069
  have eq2079121 : (M.op (σ x) (σ y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq2079105
       have i₂ := eq2078949
       grind)
    | exact superpose eq2078949 eq2079105
    | exact resolve eq2079105 eq2078949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079105
  have eq2079127 : (σ (M.op x y)) ≠ (σ (M.op y x)) := by
    first
    | (have i₁ := eq2079112
       have i₂ := eq2078949
       grind)
    | exact superpose eq2078949 eq2079112
    | exact resolve eq2079112 eq2078949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079112
  have eq2079158 : (σ (k x y)) ≠ (σ (M.op y x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq111249 x y
       have i₂ := eq2079121
       grind)
    | exact superpose eq2079121 eq111249
    | (have j0 := eq111249 x y
       grind)
    | exact resolve eq111249 eq2079121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111249 eq2079121
  have eq2079176 : (σ (M.op y x)) ≠ (σ (M.op y x)) ∨ (M.op (σ y) (σ x)) = (σ (k y x)) := by
    first
    | (have i₁ := eq2079158
       have i₂ := eq2078949
       grind)
    | exact superpose eq2078949 eq2079158
    | exact resolve eq2079158 eq2078949
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078949 eq2079158
  have eq2079177 : (M.op (σ y) (σ x)) = (σ (k y x)) := by grind
  clear eq2079176
  have eq2079195 : (σ (M.op x y)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq2079177
       have i₂ := eq2079018
       grind)
    | exact superpose eq2079018 eq2079177
    | exact resolve eq2079177 eq2079018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079018 eq2079177
  have eq2094535 : (σ (k x y)) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have j0 := eq207271 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq207271
  have eq2094536 : (σ (M.op x y)) = (σ (k x y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq2094535
       have i₂ := eq2079195
       grind)
    | exact superpose eq2079195 eq2094535
    | exact resolve eq2094535 eq2079195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2094535
  have eq2094537 : x = (M.op y y) := by
    first
    | (have r₁ := eq2094536
       have r₂ := eq235171
       grind)
    | exact resolve eq2094536 eq235171
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235171 eq2094536
  have eq2094808 : (σ (M.op y x)) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq837 y
       have i₂ := eq2094537
       grind)
    | exact superpose eq2094537 eq837
    | exact resolve eq837 eq2094537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq837 eq2094537
  have eq2095246 : (σ (M.op x y)) = (σ (M.op y x)) := by
    first
    | (have i₁ := eq2094808
       have i₂ := eq2079195
       grind)
    | exact superpose eq2079195 eq2094808
    | exact resolve eq2094808 eq2079195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2079195 eq2094808
  have eq2095307 : False := by grind
  exact eq2095307

/-- `Equation4583`: `(x ◇ x) ◇ x = (x ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = X then m(Y,X) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_x_pyy_y_pyx_x_pxy_Equation4583 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4583 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4583.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ a ∨ k a b = M.op b a :=
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
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq23 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X2
       have i₂ := eq9 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1
       have i₂ := eq9 X1 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq34 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  have eq61 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X2 X2) = X2 ∨ (k X0 X2) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X2 X2
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
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
  have eq66 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X0) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 X1 X2 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X2 X2) = X2 ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq64 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq226 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq61 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61
  have eq229 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    first
    | (have j0 := eq226 X0 X1
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq226 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq226 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq226
  have eq403 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq71 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq404 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq403 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403
  have eq409 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq404 X0
       have j1 := eq229 X0 x
       grind)
    | (have r₁ := eq404 x
       have r₂ := eq229 x x
       grind)
    | exact resolve eq404 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229 eq404
  have eq417 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq409 (σ X0)
       grind)
    | exact superpose eq409 eq15
    | exact resolve eq15 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq420 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq34 X0 X0
       have i₂ := eq409 (τ X0)
       grind)
    | exact superpose eq409 eq34
    | exact resolve eq34 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq423 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq420 X0
       have i₂ := eq409 X0
       grind)
    | exact superpose eq409 eq420
    | exact resolve eq420 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420
  have eq426 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq417 X0
       have i₂ := eq409 X0
       grind)
    | exact superpose eq409 eq417
    | exact resolve eq417 eq409
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq409 eq417
  have eq539 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k (σ X0) X1) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq426 X0
       grind)
    | exact superpose eq426 eq12
    | (have j0 := eq12 (σ X0) X1
       grind)
    | exact resolve eq12 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq543 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq23 (σ X0) X1 X2
       have i₂ := eq426 X0
       grind)
    | exact superpose eq426 eq23
    | exact resolve eq23 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq676 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (σ (M.op (M.op X0 X0) (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq426 (M.op X0 X0)
       have i₂ := eq543 X0 (σ (M.op X0 X0)) X1
       grind)
    | (have i₁ := eq426 (M.op X0 X0)
       have i₂ := eq543 X0 X1 (σ (M.op X0 X0))
       grind)
    | exact superpose eq543 eq426
    | exact resolve eq426 eq543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq695 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) X1) = (σ (M.op (M.op X0 X0) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq676 X0 X1
       have i₂ := eq9 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq676
    | exact resolve eq676 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq1184 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X2) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq695 X0 X2
       have i₂ := eq23 X0 X0 X1
       grind)
    | (have i₁ := eq695 X0 X2
       have i₂ := eq23 X0 X1 X0
       grind)
    | exact superpose eq23 eq695
    | exact resolve eq695 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq695
  have eq1628 : ∀ X0 X1 X2 : G, (M.op (σ (τ (M.op X0 X0))) X1) = (σ (M.op (τ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1184 (τ X0) X1 X2
       have i₂ := eq423 X0
       grind)
    | exact superpose eq423 eq1184
    | exact resolve eq1184 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq1721 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (σ (M.op (τ (M.op X0 X0)) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1628 X0 X1 X2
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq1628
    | exact resolve eq1628 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1628
  have eq1816 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X1) = (M.op (σ X0) X2) ∨ (σ (k X0 X3)) = (M.op (σ X0) (σ X3)) ∨ (σ X3) = (M.op (σ X3) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq23 (σ X0) X1 X2
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq23
    | (have j1 := eq66 X0 X3
       grind)
    | exact resolve eq23 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq1927 : ∀ X0 X1 X2 X3 : G, (σ X3) = (σ (M.op X3 X3)) ∨ (M.op (σ X0) X1) = (M.op (σ X0) X2) ∨ (σ (k X0 X3)) = (M.op (σ X0) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1816 X0 X1 X2 X3
       have i₂ := eq426 X3
       grind)
    | exact superpose eq426 eq1816
    | (have j0 := eq1816 X0 X1 X2 X3
       grind)
    | exact resolve eq1816 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1816
  have eq4004 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X1) = (σ (M.op (τ (σ X0)) X2)) ∨ (σ (k X0 X3)) = (M.op (σ X0) (σ X3)) ∨ (σ X3) = (M.op (σ X3) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1721 (σ X0) X1 X2
       have i₂ := eq66 X0 X1
       grind)
    | exact superpose eq66 eq1721
    | (have j1 := eq66 X0 X3
       grind)
    | exact resolve eq1721 eq66
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq1721
  have eq4177 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) X1) = (σ (M.op X0 X2)) ∨ (σ (k X0 X3)) = (M.op (σ X0) (σ X3)) ∨ (σ X3) = (M.op (σ X3) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4004 X0 X1 X2 X3
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4004
    | (have j0 := eq4004 X0 X1 X2 X3
       grind)
    | exact resolve eq4004 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4004
  have eq4189 : ∀ X0 X1 X2 X3 : G, (σ X3) = (σ (M.op X3 X3)) ∨ (M.op (σ X0) X1) = (σ (M.op X0 X2)) ∨ (σ (k X0 X3)) = (M.op (σ X0) (σ X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq4177 X0 X1 X2 X3
       have i₂ := eq426 X3
       grind)
    | exact superpose eq426 eq4177
    | (have j0 := eq4177 X0 X1 X2 X3
       grind)
    | exact resolve eq4177 eq426
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426 eq4177
  have eq80082 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k x X1)) = (M.op (σ x) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16
       have i₂ := eq1927 x (σ y) X0 X1
       grind)
    | (have i₁ := eq16
       have i₂ := eq1927 x X0 (σ y) X1
       grind)
    | exact superpose eq1927 eq16
    | (have j1 := eq1927 x X1 x X1
       grind)
    | exact resolve eq16 eq1927
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1927
  have eq80706 : ∀ X1 : G, (σ X1) = (σ (M.op X1 X1)) ∨ (σ (k x X1)) = (M.op (σ x) (σ X1)) := by
    intro X1
    first
    | (have j0 := eq80082 x X1
       have j1 := eq4189 x X1 x X1
       grind)
    | (have r₁ := eq80082 X1 X1
       have r₂ := eq4189 x X1 y x
       grind)
    | exact resolve eq80082 eq4189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4189 eq80082
  have eq99741 : ∀ X0 : G, (M.op X0 X0) = (τ (σ X0)) ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq80706 X0
       grind)
    | exact superpose eq80706 eq10
    | (have j1 := eq80706 X0
       grind)
    | exact resolve eq10 eq80706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80706
  have eq100151 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (σ (k x X0)) = (M.op (σ x) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq99741 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq99741
    | (have j0 := eq99741 X0
       grind)
    | exact resolve eq99741 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99741
  have eq104098 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq100151 y
       grind)
    | exact superpose eq100151 eq16
    | (have j1 := eq100151 y
       grind)
    | exact resolve eq16 eq100151
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100151
  have eq106369 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq104098
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq104098
    | (have j1 := eq14 y y
       grind)
    | exact resolve eq104098 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104098
  have eq106445 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq106369
  have eq106446 : y = (M.op y y) ∨ x = (M.op x x) := by grind
  clear eq106445
  have eq108327 : ∀ X0 : G, y ≠ y ∨ (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq106446
       grind)
    | exact superpose eq106446 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq106446
       grind)
    | (have r₁ := eq12 x x
       have r₂ := eq106446
       grind)
    | exact resolve eq12 eq106446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108378 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (M.op X0 (σ y)) = (k (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq539 y X0
       have i₂ := eq106446
       grind)
    | exact superpose eq106446 eq539
    | (have j0 := eq539 y X0
       grind)
    | exact resolve eq539 eq106446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq539 eq106446
  have eq108466 : ∀ X0 : G, (M.op X0 (σ y)) = (k (σ y) X0) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq108378 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108378
  have eq108468 : ∀ X0 : G, (k y X0) = (M.op X0 y) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have j0 := eq108327 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108327
  have eq123660 : ∀ X0 : G, (k (σ y) X0) = (σ (M.op (τ X0) y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq18 X0 y
       have i₂ := eq108468 (τ X0)
       grind)
    | exact superpose eq108468 eq18
    | exact resolve eq18 eq108468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq108468
  have eq141342 : ∀ X0 : G, (σ (k y X0)) = (M.op (σ X0) (σ y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq15 y X0
       have i₂ := eq108466 (σ X0)
       grind)
    | exact superpose eq108466 eq15
    | exact resolve eq15 eq108466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108466
  have eq239485 : ∀ X0 : G, (σ (M.op X0 y)) = (k (σ y) (σ X0)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq123660 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq123660
    | exact resolve eq123660 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123660
  have eq239564 : ∀ X0 : G, (σ (k y X0)) = (σ (M.op X0 y)) ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq239485 X0
       have i₂ := eq15 y X0
       grind)
    | exact superpose eq15 eq239485
    | exact resolve eq239485 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239485
  have eq243138 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq141342 x
       grind)
    | exact superpose eq141342 eq16
    | exact resolve eq16 eq141342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141342
  have eq243356 : x = (M.op x x) := by
    first
    | (have r₁ := eq243138
       have r₂ := eq239564 x
       grind)
    | exact resolve eq243138 eq239564
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239564 eq243138
  have eq243512 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq543 x X1 x
       have i₂ := eq243356
       grind)
    | exact superpose eq243356 eq543
    | exact resolve eq543 eq243356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq243526 : ∀ X0 X1 : G, (M.op (σ x) X0) = (σ (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1184 x X1 x
       have i₂ := eq243356
       grind)
    | exact superpose eq243356 eq1184
    | exact resolve eq1184 eq243356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1184 eq243356
  have eq245499 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq243512 (σ y) X0
       grind)
    | (have i₁ := eq16
       have i₂ := eq243512 X0 (σ y)
       grind)
    | exact superpose eq243512 eq16
    | exact resolve eq16 eq243512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243512
  have eq245641 : False := by grind
  exact eq245641

/-- `Equation4583`: `(x ◇ x) ◇ x = (x ◇ x) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxx_y_pyx_x_pxy_Equation4583 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4583 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4583.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op (M.op X0 X0) X0) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
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
  have eq25 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X0 X0) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X2
       have i₂ := eq9 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1
       have i₂ := eq9 X1 X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq84 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op X0 (τ X1))) ∨ (M.op (τ X1) (τ X1)) = X0 ∨ (M.op X0 X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq20 X1 X0
       have i₂ := eq14 X0 (τ X1)
       grind)
    | exact superpose eq14 eq20
    | (have j1 := eq14 X0 (τ X1)
       grind)
    | exact resolve eq20 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq690 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    grind
  clear eq77
  have eq2162 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq86 X1 X0
       grind)
    | exact superpose eq86 eq10
    | (have j1 := eq86 X1 X0
       grind)
    | exact resolve eq10 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq11238 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq690 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq11240 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11238 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11238
  have eq11241 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq11240 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11240
  have eq11377 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq11241 (σ X0)
       grind)
    | exact superpose eq11241 eq15
    | exact resolve eq15 eq11241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11396 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq11377 X0
       have i₂ := eq11241 X0
       grind)
    | exact superpose eq11241 eq11377
    | exact resolve eq11377 eq11241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11241 eq11377
  have eq13307 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq13309 : ∀ X0 X1 X2 : G, (M.op (σ (M.op X0 X0)) X1) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25 (σ X0) X1 X2
       have i₂ := eq11396 X0
       grind)
    | exact superpose eq11396 eq25
    | exact resolve eq25 eq11396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13438 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq13307 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq13307
    | exact resolve eq13307 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13307
  have eq13468 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq13438
  have eq16036 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) (M.op X0 X0))) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq11396 (M.op X0 X0)
       have i₂ := eq13309 X0 (σ (M.op X0 X0)) X1
       grind)
    | (have i₁ := eq11396 (M.op X0 X0)
       have i₂ := eq13309 X0 X1 (σ (M.op X0 X0))
       grind)
    | exact superpose eq13309 eq11396
    | exact resolve eq11396 eq13309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16153 : ∀ X0 X1 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16036 X0 X1
       have i₂ := eq9 X0 (M.op X0 X0)
       grind)
    | exact superpose eq9 eq16036
    | exact resolve eq16036 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16036
  have eq19450 : ∀ X0 X1 X2 : G, (σ (M.op (M.op X0 X0) X1)) = (M.op (σ (M.op X0 X0)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq16153 X0 X2
       have i₂ := eq25 X0 X0 X1
       grind)
    | (have i₁ := eq16153 X0 X2
       have i₂ := eq25 X0 X1 X0
       grind)
    | exact superpose eq25 eq16153
    | exact resolve eq16153 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq16153
  have eq20148 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (k (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq20744 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20148 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq20148
    | (have j0 := eq20148 X0 X1
       grind)
    | exact resolve eq20148 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20148
  have eq135963 : ∀ X0 X1 : G, (τ (M.op (σ X0) (σ X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1
       have i₂ := eq2162 X1 X0
       grind)
    | exact superpose eq2162 eq10
    | (have j1 := eq2162 X1 X0
       grind)
    | exact resolve eq10 eq2162
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2162
  have eq136883 : ∀ X0 X1 : G, (τ (σ (M.op X0 X0))) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq135963 X0 X1
       have i₂ := eq11396 X0
       grind)
    | exact superpose eq11396 eq135963
    | (have j0 := eq135963 X0 X1
       grind)
    | exact resolve eq135963 eq11396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135963
  have eq138117 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (τ (M.op (σ X1) (σ X1))) = X0 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq136883 X0 X1
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq136883
    | (have j0 := eq136883 X0 X1
       grind)
    | exact resolve eq136883 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136883
  have eq139045 : ∀ X0 X1 : G, (τ (σ (M.op X1 X1))) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq138117 X0 X1
       have i₂ := eq11396 X1
       grind)
    | exact superpose eq11396 eq138117
    | (have j0 := eq138117 X0 X1
       grind)
    | exact resolve eq138117 eq11396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11396 eq138117
  have eq139638 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq139045 X0 X1
       have i₂ := eq10 (M.op X1 X1)
       grind)
    | exact superpose eq10 eq139045
    | (have j0 := eq139045 X0 X1
       grind)
    | exact resolve eq139045 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139045
  have eq1946841 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq139638 x y
       grind)
    | exact superpose eq139638 eq16
    | (have j1 := eq139638 x y
       grind)
    | exact resolve eq16 eq139638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139638
  have eq1946848 : x = (M.op y y) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq20744 x y
       grind)
    | (have r₁ := eq1946841
       have r₂ := eq20744 y x
       grind)
    | exact resolve eq1946841 eq20744
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20744 eq1946841
  have eq1946895 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (σ x) X1) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq13309 y X1 x
       have i₂ := eq1946848
       grind)
    | exact superpose eq1946848 eq13309
    | exact resolve eq13309 eq1946848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13309
  have eq1946937 : ∀ X0 X1 : G, (M.op (σ x) X1) = (σ (M.op x X0)) ∨ y = (M.op x x) := by
    intro X0 X1
    first
    | (have i₁ := eq19450 y X1 x
       have i₂ := eq1946848
       grind)
    | exact superpose eq1946848 eq19450
    | exact resolve eq19450 eq1946848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19450 eq1946848
  have eq1953111 : ∀ X0 : G, (σ (M.op x y)) ≠ (M.op (σ x) X0) ∨ y = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq1946895 (σ y) X0
       grind)
    | (have i₁ := eq16
       have i₂ := eq1946895 X0 (σ y)
       grind)
    | exact superpose eq1946895 eq16
    | exact resolve eq16 eq1946895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1946895
  have eq1953122 : y = (M.op x x) := by
    first
    | (have r₁ := eq1953111 x
       have r₂ := eq1946937 y x
       grind)
    | exact resolve eq1953111 eq1946937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1946937 eq1953111
  have eq1953240 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13468 x
       have i₂ := eq1953122
       grind)
    | exact superpose eq1953122 eq13468
    | exact resolve eq13468 eq1953122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13468 eq1953122
  have eq1953812 : False := by grind
  exact eq1953812
