import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation452`: `x = x ◇ (y ◇ (z ◇ (y ◇ z)))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_y_pyx_Equation452 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law452 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law452.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
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
  clear eq36
  have eq51 : (σ (k x x)) = (M.op (σ x) (σ x)) := by grind
  clear eq48
  have eq52 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by grind
  clear eq51
  have eq53 : ∀ X0 : G, (M.op X0 (M.op x (M.op y (M.op x y)))) = X0 := by
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
  have eq68 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq69 : y ≠ (M.op x y) ∨ x = y ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 y x
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq87 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq94 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq87
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq87
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq87 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq99 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq87
       grind)
    | exact superpose eq87 eq16
    | exact resolve eq16 eq87
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq100 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq94
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq94
    | exact resolve eq94 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq101 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq21 eq100
    | exact resolve eq100 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq102 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq101
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101
    | exact resolve eq101 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq117 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq120 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq117
  have eq121 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq120
  have eq160 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq121 eq16
    | exact resolve eq16 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq375 : ∀ X0 X1 : G, (M.op X1 (M.op (σ X0) (M.op (σ X0) (σ (M.op X0 X0))))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (σ X0) (σ X0)
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq14
    | exact resolve eq14 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq748 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ X1) (M.op (σ X0) (σ (k X0 X1))))) = X2 ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X2 (σ X1) (σ X0)
       have i₂ := eq75 X0 X1
       grind)
    | exact superpose eq75 eq14
    | (have j1 := eq75 X0 X1
       grind)
    | exact resolve eq14 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq773 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq102 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq774 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq773
    | exact resolve eq773 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq773
  have eq777 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have r₁ := eq774
       have r₂ := eq28
       grind)
    | exact resolve eq774 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq774
  have eq779 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq27 eq777
    | exact resolve eq777 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq777
  have eq781 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq779 eq70
    | (have r₁ := eq70
       have r₂ := eq779
       grind)
    | exact resolve eq70 eq779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq779
  have eq784 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq781
  have eq785 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq784
  have eq788 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq785 eq102
    | exact resolve eq102 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102
  have eq789 : (τ (σ x)) = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq785 eq99
    | exact resolve eq99 eq785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99 eq785
  have eq792 : (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by grind
  clear eq788
  have eq796 : x = (k y x) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq29 eq789
    | exact resolve eq789 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789
  have eq799 : x = (k y x) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq796
       have r₂ := eq69
       grind)
    | exact resolve eq796 eq69
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq796
  have eq852 : y = (τ (σ x)) ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq792 eq30
    | exact resolve eq30 eq792
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq792
  have eq871 : x = y ∨ y = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq29 eq852
    | exact resolve eq852 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq852
  have eq872 : (σ (M.op x y)) = (σ x) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq871
  have eq912 : x = (τ (σ (M.op x y))) ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq872 eq29
    | exact resolve eq29 eq872
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq872
  have eq935 : y = (M.op x y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq912
    | exact resolve eq912 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq912
  have eq938 : (σ y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq935 eq21
    | exact resolve eq21 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq940 : ∀ X0 : G, (M.op X0 (M.op x (M.op y y))) = X0 ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq935 eq53
    | exact resolve eq53 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq961 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq938
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq938
    | exact resolve eq938 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq938
  have eq2096 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq375 (M.op X0 (M.op X1 (M.op X0 X1))) X2
       have i₂ := eq14 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq14 eq375
    | exact resolve eq375 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq375
  have eq2138 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1))))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2096 X0 X1 X2
       have i₂ := eq45 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | exact superpose eq45 eq2096
    | exact resolve eq2096 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2096
  have eq2156 : ∀ X0 X1 X2 : G, (M.op X2 (M.op (σ (M.op X0 (M.op X1 (M.op X0 X1)))) (σ (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2138 X0 X1 X2
       have i₂ := eq14 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq14 eq2138
    | exact resolve eq2138 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2138
  have eq2167 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op (M.op X0 (M.op X1 (M.op X0 X1))) (M.op X0 (M.op X1 (M.op X0 X1)))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2156 X0 X1 X2
       have i₂ := eq45 (M.op X0 (M.op X1 (M.op X0 X1)))
       grind)
    | exact superpose eq45 eq2156
    | exact resolve eq2156 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq2156
  have eq2174 : ∀ X0 X1 X2 : G, (M.op X2 (σ (M.op X0 (M.op X1 (M.op X0 X1))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2167 X0 X1 X2
       have i₂ := eq14 (M.op X0 (M.op X1 (M.op X0 X1))) X0 X1
       grind)
    | exact superpose eq14 eq2167
    | exact resolve eq2167 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2167
  have eq8371 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq748 y x X0
       have i₂ := eq799
       grind)
    | exact superpose eq799 eq748
    | (have j0 := eq748 y x x
       grind)
    | exact resolve eq748 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq748 eq799
  have eq8556 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8371 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8371
    | (have j0 := eq8371 X0
       grind)
    | exact resolve eq8371 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8371
  have eq8642 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8556 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8556
    | (have j0 := eq8556 X0
       grind)
    | exact resolve eq8556 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8556
  have eq8726 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8642 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8642
    | (have j0 := eq8642 X0
       grind)
    | exact resolve eq8642 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8642
  have eq8781 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8726 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8726
    | (have j0 := eq8726 X0
       grind)
    | exact resolve eq8726 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8726
  have eq8833 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq27 eq8781
    | (have j0 := eq8781 X0
       grind)
    | exact resolve eq8781 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8781
  have eq8881 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8833 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8833
    | (have j0 := eq8833 X0
       grind)
    | exact resolve eq8833 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8833
  have eq8907 : ∀ X0 : G, (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq8881 X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq8881
    | (have j0 := eq8881 X0
       grind)
    | exact resolve eq8881 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8881
  have eq8908 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq8907 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8907
  have eq1642325 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    by_contra hcon
    push Not at hcon
    obtain ⟨g0, g1, g2, g3⟩ := hcon
    have f1642325_16 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
      intro X0
      grind
    have f1642325_22 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X1 X2)))) = X0 := by
      intro X0 X1 X2
      grind
    have f1642325_25 : X0 ≠ (M.op X0 (σ y)) := by grind
    have f1642325_26 : (σ y) ≠ (M.op (σ x) (σ y)) := by grind
    have f1642325_27 : (σ x) ≠ (σ y) := by grind
    have f1642325_28 : x ≠ y := by grind
    have f1642325_30 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ (σ x) = (σ y) ∨ x = y := by
      intro X0
      first
      | (have j0 := f1642325_16 X0
         grind)
      | (have r₁ := f1642325_16 X0
         have r₂ := f1642325_26
         grind)
      | exact resolve f1642325_16 f1642325_26
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1642325_31 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 ∨ x = y := by
      intro X0
      first
      | (have j0 := f1642325_30 X0
         grind)
      | (have r₁ := f1642325_30 X0
         have r₂ := f1642325_27
         grind)
      | exact resolve f1642325_30 f1642325_27
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1642325_32 : ∀ X0 : G, (M.op X0 (M.op (σ x) (M.op (σ y) (σ x)))) = X0 := by
      intro X0
      first
      | (have j0 := f1642325_31 X0
         grind)
      | (have r₁ := f1642325_31 X0
         have r₂ := f1642325_28
         grind)
      | exact resolve f1642325_31 f1642325_28
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1642325_48 : ∀ X0 : G, (M.op X0 (σ y)) = X0 := by
      intro X0
      first
      | (have i₁ := f1642325_22 X0 (σ y) (σ x)
         have i₂ := f1642325_32 (σ y)
         grind)
      | exact superpose f1642325_32 f1642325_22
      | exact resolve f1642325_22 f1642325_32
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1642325_51 : X0 ≠ X0 := by
      first
      | (have i₁ := f1642325_25
         have i₂ := f1642325_48 X0
         grind)
      | exact superpose f1642325_48 f1642325_25
      | (have r₁ := f1642325_25
         have r₂ := f1642325_48 X0
         grind)
      | exact resolve f1642325_25 f1642325_48
      | grind
      | grind (splits := 40)
      | grind (splits := 40) (ematch := 20)
    have f1642325_55 : False := by grind
    exact f1642325_55
  clear eq8908
  have eq1643060 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq961 eq1642325
    | exact resolve eq1642325 eq961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq961 eq1642325
  have eq1643573 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1643060 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1643060
  have eq1643791 : ∀ X0 : G, (M.op X0 (σ (M.op x y))) = X0 ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1643573 X0
       grind)
    | (have r₁ := eq1643573 X0
       have r₂ := eq28
       grind)
    | exact resolve eq1643573 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1643573
  have eq1644388 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1643791 eq160
    | exact resolve eq160 eq1643791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160 eq1643791
  have eq1644474 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq1644388
    | exact resolve eq1644388 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1644388
  have eq1644726 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = y ∨ x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq935 eq1644474
    | exact resolve eq1644474 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1644474
  have eq1644881 : y = (M.op y y) ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1644726
  have eq1645123 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq940 X0
       have i₂ := eq1644881
       grind)
    | exact superpose eq1644881 eq940
    | exact resolve eq940 eq1644881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq940 eq1644881
  have eq1645192 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have j0 := eq1645123 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645123
  have eq1645216 : ∀ X0 : G, (M.op X0 (M.op x y)) = X0 ∨ x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq1645192 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq1645192
    | (have j0 := eq1645192 X0
       grind)
    | exact resolve eq1645192 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645192
  have eq1645392 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = y ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq935 eq1645216
    | exact resolve eq1645216 eq935
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq935 eq1645216
  have eq1645980 : ∀ X0 : G, (M.op X0 y) = X0 ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq1645392 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645392
  have eq1646950 : x = (M.op x y) ∨ x = y ∨ (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1645980 x
       grind)
    | exact superpose eq1645980 eq19
    | (have j1 := eq1645980 x
       grind)
    | exact resolve eq19 eq1645980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1645980
  have eq1646995 : (σ (M.op x y)) = (σ x) ∨ x = y ∨ x = (M.op x y) := by grind
  clear eq1646950
  have eq1647454 : x = (τ (σ (M.op x y))) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq1646995 eq29
    | exact resolve eq29 eq1646995
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1646995
  have eq1648766 : x = (M.op x y) ∨ x = y ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq1647454
    | exact resolve eq1647454 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq1647454
  have eq1648767 : x = (M.op x y) ∨ x = y := by grind
  clear eq1648766
  have eq1648799 : (σ x) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq1648767 eq21
    | exact resolve eq21 eq1648767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1648801 : ∀ X0 : G, (M.op X0 (M.op x (M.op y x))) = X0 ∨ x = y := by
    intro X0
    first
    | exact superpose eq1648767 eq53
    | exact resolve eq53 eq1648767
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq1648767
  have eq1649783 : (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | (have i₁ := eq1648799
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1648799
    | exact resolve eq1648799 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1648799
  have eq1649816 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = y := by
    first
    | exact superpose eq1649783 eq27
    | exact resolve eq27 eq1649783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649783
  have eq1674490 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq2174 y x X0
       have i₂ := eq1648801 y
       grind)
    | exact superpose eq1648801 eq2174
    | exact resolve eq2174 eq1648801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2174 eq1648801
  have eq1675182 : ∀ X0 : G, (M.op X0 (σ y)) = X0 ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq1674490 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1674490
    | (have j0 := eq1674490 X0
       grind)
    | exact resolve eq1674490 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1674490
  have eq1676526 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq1675182 eq1649816
    | exact resolve eq1649816 eq1675182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1649816 eq1675182
  have eq1676593 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y := by grind
  clear eq1676526
  have eq1676652 : x = y := by
    first
    | (have r₁ := eq1676593
       have r₂ := eq28
       grind)
    | exact resolve eq1676593 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1676593
  have eq1676906 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq1676652
       grind)
    | exact superpose eq1676652 eq19
    | exact resolve eq19 eq1676652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq1676907 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq1676652
       grind)
    | exact superpose eq1676652 eq25
    | exact resolve eq25 eq1676652
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq1676652
  have eq1677321 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq1676907
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1676907
    | exact resolve eq1676907 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq1676907
  have eq1681161 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq1677321 eq27
    | exact resolve eq27 eq1677321
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq1677321
  have eq1682235 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq1681161 eq68
    | exact resolve eq68 eq1681161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq1681161
  have eq1682316 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq1682235
       have i₂ := eq1676906
       grind)
    | exact superpose eq1676906 eq1682235
    | exact resolve eq1682235 eq1676906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1676906 eq1682235
  have eq1688008 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq1682316 eq15
    | exact resolve eq15 eq1682316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1682316
  have eq1688767 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq1688008
    | exact resolve eq1688008 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq1688008
  have eq1688937 : False := by grind
  exact eq1688937

/-- `Equation4521`: `x ◇ (y ◇ z) = (x ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(X,Y) else if m(Y,Y) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyy_y_pxy_x_pxy_Equation4521 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law4521 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4521.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq42 : ∀ X0 : G, (σ (k x (τ X0))) = (k (σ x) X0) := by
    intro X0
    first
    | (have i₁ := eq35 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq35
    | exact resolve eq35 eq15
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
  have eq56 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 X1 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X0 X1 X2 x
       have i₂ := eq14 X0 X3 X4 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) ≠ (M.op X0 X3) ∨ (M.op X0 (M.op X1 X2)) = (k (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X0 X3) X3
       have i₂ := eq14 X0 X1 X2 X3
       grind)
    | exact superpose eq14 eq13
    | (have r₁ := eq13 (M.op X0 (M.op X1 X2)) (M.op X1 X2)
       have r₂ := eq14 X0 X1 X2 (M.op X1 X2)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq88 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X1 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq11 X0 X1
       have r₂ := eq13 X1 X1
       grind)
    | exact resolve eq11 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq81
       grind)
    | exact superpose eq81 eq16
    | exact resolve eq16 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq88 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq88
    | (have j0 := eq88 X0 (σ X1)
       grind)
    | exact resolve eq88 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq88 x y
       grind)
    | exact superpose eq88 eq44
    | (have j1 := eq88 x y
       grind)
    | exact resolve eq44 eq88
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
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
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq117
    | exact resolve eq117 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq132 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq136 : (σ (k (k x x) x)) = (k (k (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq39 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq39
    | exact resolve eq39 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq43
  have eq209 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq56
    | (have j0 := eq56 x y
       grind)
    | exact resolve eq56 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq224 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq57 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq57
    | (have j0 := eq57 x y
       grind)
    | exact resolve eq57 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq259 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq294 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq16 (k x (τ X0))
       have i₂ := eq42 X0
       grind)
    | exact superpose eq42 eq16
    | exact resolve eq16 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42
  have eq396 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 x y X1 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq58
    | (have j0 := eq58 X0 X1 X2 x y
       grind)
    | exact resolve eq58 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq906 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq396 X0 x x
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq396
    | (have j1 := eq14 X0 x y X1
       grind)
    | exact resolve eq396 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1396 : ∀ X0 X1 X2 X3 : G, (M.op (σ X0) (M.op X2 X3)) = (M.op (σ (k X0 X1)) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 (σ X0) X2 X3 (σ X1)
       have i₂ := eq100 X0 X1
       grind)
    | exact superpose eq100 eq14
    | (have j1 := eq100 X0 X1
       grind)
    | exact resolve eq14 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1411 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq100 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1421 : ∀ X0 X1 : G, (M.op (σ (k X0 X1)) (σ X1)) = (M.op (σ X0) (M.op x y)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1396 X0 X1 x x
       have i₂ := eq396 (σ X0) x x
       grind)
    | (have i₁ := eq1396 X0 X1 x y
       have i₂ := eq396 (σ X0) X1 x
       grind)
    | exact superpose eq396 eq1396
    | (have j0 := eq1396 X0 X1 x y
       grind)
    | exact resolve eq1396 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq1616 : ∀ X0 X1 X2 X3 : G, (M.op X0 X3) ≠ (M.op X0 (M.op x y)) ∨ (M.op X0 (M.op X1 X2)) = (k (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq70 X0 X1 X2 X3
       have i₂ := eq396 X0 X1 X2
       grind)
    | (have i₁ := eq70 X0 x y X3
       have i₂ := eq396 X0 X1 X2
       grind)
    | exact superpose eq396 eq70
    | (have j0 := eq70 X0 x y X3
       grind)
    | (have r₁ := eq70 X0 X1 X2 (M.op x y)
       have r₂ := eq396 X0 X1 X2
       grind)
    | (have r₁ := eq70 X0 x y (M.op X1 X2)
       have r₂ := eq396 X0 X1 X2
       grind)
    | exact resolve eq70 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1617 : ∀ X0 X3 : G, (M.op X0 X3) ≠ (M.op X0 (M.op x y)) ∨ (k (M.op X0 X3) X3) = (M.op X0 (M.op x y)) := by
    intro X0 X3
    first
    | (have i₁ := eq1616 X0 x x X3
       have i₂ := eq396 X0 x x
       grind)
    | (have i₁ := eq1616 X0 x y X3
       have i₂ := eq396 X0 x x
       grind)
    | exact superpose eq396 eq1616
    | (have j0 := eq1616 X0 x y X3
       grind)
    | (have r₁ := eq1616 X0 x x (M.op x x)
       have r₂ := eq396 X0 x x
       grind)
    | (have r₁ := eq1616 X0 x x (M.op x y)
       have r₂ := eq396 X0 x y
       grind)
    | exact resolve eq1616 eq396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1616
  have eq1652 : ∀ X0 : G, (M.op X0 (M.op x y)) = (k (M.op X0 (M.op x y)) (M.op x y)) := by
    intro X0
    first
    | (have j0 := eq1617 X0 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1617
  have eq1758 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq259 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq259
    | exact resolve eq259 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq259
  have eq1976 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq118 eq88
    | (have j0 := eq88 x (σ y)
       grind)
    | exact resolve eq88 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq1977 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq1976
    | exact resolve eq1976 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1976
  have eq1980 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1977
       have r₂ := eq27
       grind)
    | exact resolve eq1977 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1977
  have eq1986 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1980 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq1980
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq1980
       grind)
    | exact resolve eq13 eq1980
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1980
  have eq2003 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1986
  have eq2023 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq2003 eq93
    | exact resolve eq93 eq2003
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq2003
  have eq2027 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq2023
    | exact resolve eq2023 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq2023
  have eq2073 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq88 y y
       have i₂ := eq2027
       grind)
    | exact superpose eq2027 eq88
    | (have j0 := eq88 x y
       grind)
    | exact resolve eq88 eq2027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2027
  have eq2074 : y = (M.op y y) := by grind
  clear eq2073
  have eq2078 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq2074
       grind)
    | exact superpose eq2074 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq2074
       grind)
    | exact resolve eq13 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2085 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq56 y y
       have i₂ := eq2074
       grind)
    | exact superpose eq2074 eq56
    | exact resolve eq56 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq2090 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq396 X0 y y
       have i₂ := eq2074
       grind)
    | exact superpose eq2074 eq396
    | exact resolve eq396 eq2074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq396 eq2074
  have eq2093 : y = (k y y) := by grind
  clear eq2078
  have eq2100 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq209 eq2085
    | exact resolve eq2085 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq2085
  have eq2108 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq2100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2100
    | exact resolve eq2100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2100
  have eq2118 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq81
       have i₂ := eq2093
       grind)
    | exact superpose eq2093 eq81
    | exact resolve eq81 eq2093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq2093
  have eq2122 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq2118
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq2118
    | exact resolve eq2118 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq2118
  have eq2163 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2108 eq1652
    | exact resolve eq1652 eq2108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1652
  have eq2199 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq2122 eq88
    | (have j0 := eq88 x (σ y)
       grind)
    | exact resolve eq88 eq2122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2122
  have eq2200 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq2199
  have eq2249 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2163 eq132
    | exact resolve eq132 eq2163
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq2163
  have eq2253 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq2249
    | exact resolve eq2249 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2249
  have eq2265 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq2200 eq57
    | exact resolve eq57 eq2200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq2200
  have eq2281 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq224 eq2265
    | exact resolve eq2265 eq224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq224 eq2265
  have eq2290 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq26 eq2281
    | exact resolve eq2281 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq2281
  have eq2308 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2253 eq88
    | (have j0 := eq88 x (σ (M.op x y))
       grind)
    | exact resolve eq88 eq2253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88 eq2253
  have eq2309 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2308
  have eq2509 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq2309 eq906
    | exact resolve eq906 eq2309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2517 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq2309 eq2509
    | exact resolve eq2509 eq2309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2309 eq2509
  have eq3052 : (σ (M.op x y)) = (M.op (σ (M.op x y)) y) := by
    first
    | exact superpose eq2517 eq2090
    | exact resolve eq2090 eq2517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2517
  have eq3053 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq2290 eq2090
    | exact resolve eq2090 eq2290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2290
  have eq11416 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1411 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq1411
    | (have j0 := eq1411 (τ X0)
       grind)
    | exact resolve eq1411 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1411
  have eq11449 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq11416 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq11416
    | (have j0 := eq11416 X0
       grind)
    | exact resolve eq11416 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11416
  have eq11460 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq11449 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq11449
    | (have j0 := eq11449 X0
       grind)
    | exact resolve eq11449 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11449
  have eq19626 : ∀ X0 X1 : G, (M.op (σ (k X0 X1)) (σ X1)) = (M.op (σ X0) y) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | exact superpose eq2090 eq1421
    | (have j0 := eq1421 X0 X1
       grind)
    | exact resolve eq1421 eq2090
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1421 eq2090
  have eq19929 : ∀ X0 X1 : G, (σ (k (k X0 X1) X1)) = (M.op (σ X0) y) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq100 (k X0 X1) X1
       have i₂ := eq19626 X0 X1
       grind)
    | exact superpose eq19626 eq100
    | (have j0 := eq100 X0 X1
       have j1 := eq19626 X0 X1
       grind)
    | exact resolve eq100 eq19626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq19626
  have eq19978 : ∀ X0 X1 : G, (σ (k (k X0 X1) X1)) = (M.op (σ X0) y) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq19929 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19929
  have eq76087 : ∀ X0 : G, (M.op (σ x) y) = (σ (k (τ (k (σ x) X0)) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq19978 x (τ X0)
       have i₂ := eq294 X0
       grind)
    | exact superpose eq294 eq19978
    | (have j0 := eq19978 X0 (τ X0)
       grind)
    | exact resolve eq19978 eq294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq294
  have eq76566 : ∀ X0 : G, (M.op (σ x) y) = (k (k (σ x) X0) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq76087 X0
       have i₂ := eq34 (k sF2 X0) (τ X0)
       grind)
    | exact superpose eq34 eq76087
    | (have j0 := eq76087 X0
       grind)
    | exact resolve eq76087 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76087
  have eq76789 : ∀ X0 : G, (M.op (σ x) y) = (k (k (σ x) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq76566 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq76566
    | (have j0 := eq76566 X0
       grind)
    | exact resolve eq76566 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76566
  have eq76895 : ∀ X0 : G, (M.op (σ x) y) = (k (k (σ x) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq76789 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq76789
    | (have j0 := eq76789 X0
       grind)
    | exact resolve eq76789 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76789
  have eq76955 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (k (σ x) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | exact superpose eq3053 eq76895
    | (have j0 := eq76895 X0
       grind)
    | exact resolve eq76895 eq3053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76895
  have eq76984 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (k (σ x) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq76955 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq76955
    | (have j0 := eq76955 X0
       grind)
    | exact resolve eq76955 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76955
  have eq530015 : ∀ X0 X1 : G, (M.op (σ (τ X0)) y) = (σ (k (τ (k X0 X1)) (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq19978 (τ X0) (τ X1)
       have i₂ := eq1758 X1 X0
       grind)
    | exact superpose eq1758 eq19978
    | (have j0 := eq19978 X0 (τ X1)
       grind)
    | exact resolve eq19978 eq1758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1758 eq19978
  have eq530090 : ∀ X0 X1 : G, (M.op (σ (τ X0)) y) = (k (k X0 X1) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq530015 X0 X1
       have i₂ := eq34 (k X0 X1) (τ X1)
       grind)
    | exact superpose eq34 eq530015
    | (have j0 := eq530015 X0 X1
       grind)
    | exact resolve eq530015 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq530015
  have eq530305 : ∀ X0 X1 : G, (k (k X0 X1) X1) = (M.op (σ (τ X0)) y) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq530090 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq530090
    | (have j0 := eq530090 X0 X1
       grind)
    | exact resolve eq530090 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530090
  have eq530501 : ∀ X0 X1 : G, (k (k X0 X1) X1) = (M.op X0 y) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq530305 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq530305
    | (have j0 := eq530305 X0 X1
       grind)
    | exact resolve eq530305 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530305
  have eq530637 : ∀ X0 X1 : G, (k (k X0 X1) X1) = (M.op X0 y) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq530501 X0 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq530501
    | (have j0 := eq530501 X0 X1
       grind)
    | exact resolve eq530501 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq530501
  have eq1875619 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq136
       have i₂ := eq530637 x x
       grind)
    | exact superpose eq530637 eq136
    | (have j1 := eq530637 x x
       grind)
    | exact resolve eq136 eq530637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136 eq530637
  have eq1875864 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq1875619
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1875619
    | exact resolve eq1875619 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1875619
  have eq1877384 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq1875864
    | exact resolve eq1875864 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1875864
  have eq1900580 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1877384 eq76984
    | (have j0 := eq76984 (σ x)
       grind)
    | exact resolve eq76984 eq1877384
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76984 eq1877384
  have eq1900699 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq1900580
       have r₂ := eq27
       grind)
    | exact resolve eq1900580 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1900580
  have eq1900762 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1900699 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq1900699
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq1900699
       grind)
    | exact resolve eq13 eq1900699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1900699
  have eq1900854 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq1900762
  have eq1903170 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq1900854 eq49
    | exact resolve eq49 eq1900854
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq1900854
  have eq1903362 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq1903170
    | exact resolve eq1903170 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq1903170
  have eq1903367 : x = (M.op x x) := by
    first
    | (have j1 := eq11460 x
       grind)
    | (have r₁ := eq1903362
       have r₂ := eq11460 x
       grind)
    | exact resolve eq1903362 eq11460
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11460 eq1903362
  have eq1903399 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq906 x x
       have i₂ := eq1903367
       grind)
    | exact superpose eq1903367 eq906
    | exact resolve eq906 eq1903367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq906
  have eq1903507 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq2108 eq1903399
    | exact resolve eq1903399 eq2108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2108 eq1903399
  have eq1903545 : x = (M.op x y) := by
    first
    | (have i₁ := eq1903507
       have i₂ := eq1903367
       grind)
    | exact superpose eq1903367 eq1903507
    | exact resolve eq1903507 eq1903367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1903367 eq1903507
  have eq1903604 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq1903545 eq20
    | exact resolve eq20 eq1903545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq1903545
  have eq1904661 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq1903604
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1903604
    | exact resolve eq1903604 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq1903604
  have eq1904802 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) y) := by
    first
    | exact superpose eq1904661 eq3053
    | exact resolve eq3053 eq1904661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3053 eq1904661
  have eq1905372 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq3052 eq1904802
    | exact resolve eq1904802 eq3052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3052 eq1904802
  have eq1905512 : False := by grind
  exact eq1905512

/-- `Equation4521`: `x ◇ (y ◇ z) = (x ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(Y,Y) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_pxy_pxx_pxy_Equation4521 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4521 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4521.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq52 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X4) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 X0 x x X4
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 X1 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq58 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X0 X1 X2 x
       have i₂ := eq14 X0 X3 X4 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq80 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq82 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
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
  have eq92 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq80
       grind)
    | exact superpose eq80 eq16
    | exact resolve eq16 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82 (σ X0) (σ X1)
       have i₂ := eq10 X0 X1
       grind)
    | exact superpose eq10 eq82
    | (have j0 := eq82 X0 (σ X1)
       grind)
    | exact resolve eq82 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq82 x y
       grind)
    | exact superpose eq82 eq44
    | (have j1 := eq82 x y
       grind)
    | exact resolve eq44 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq114 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq106
    | exact resolve eq106 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq114
    | exact resolve eq114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq132 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq150 : (σ (k (k x x) x)) = (k (k (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq39 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq39
    | exact resolve eq39 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq43
  have eq209 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq56 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq56
    | (have j0 := eq56 x y
       grind)
    | exact resolve eq56 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq56 x x
       have i₂ := eq14 x x x X0
       grind)
    | exact superpose eq14 eq56
    | exact resolve eq56 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq220 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq57 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq57
    | (have j0 := eq57 x y
       grind)
    | exact resolve eq57 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq258 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq296 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq311 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | exact superpose eq209 eq212
    | exact resolve eq212 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq403 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq58 X0 x y X1 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq58
    | (have j0 := eq58 X0 X1 X2 x y
       grind)
    | exact resolve eq58 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq881 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq403 X0 x x
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq403
    | (have j1 := eq14 X0 x y X1
       grind)
    | exact resolve eq403 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1401 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) (σ X1)) = (M.op (M.op (σ X0) X2) X2) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (σ X0) X2 (σ X1)
       have i₂ := eq98 X0 X1
       grind)
    | exact superpose eq98 eq52
    | (have j1 := eq98 X0 X1
       grind)
    | exact resolve eq52 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq1414 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq98 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1424 : ∀ X0 X1 : G, (M.op (σ (k X0 X1)) (σ X1)) = (M.op (σ X0) (M.op x y)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1401 X0 X1 x
       have i₂ := eq881 (σ X0) x
       grind)
    | exact superpose eq881 eq1401
    | (have j0 := eq1401 X0 X1 x
       grind)
    | exact resolve eq1401 eq881
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1401
  have eq1442 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq258 X1 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq258
    | exact resolve eq258 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq258
  have eq1538 : ∀ X0 : G, (k x (τ X0)) = (τ (k (σ x) X0)) := by
    intro X0
    first
    | (have i₁ := eq296 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq296
    | (have j0 := eq296 x X0
       grind)
    | exact resolve eq296 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq296
  have eq1623 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq115 eq82
    | (have j0 := eq82 x (σ y)
       grind)
    | exact resolve eq82 eq115
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq1624 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq26 eq1623
    | exact resolve eq1623 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1623
  have eq1627 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq1624
       have r₂ := eq27
       grind)
    | exact resolve eq1624 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1624
  have eq1682 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1627 eq13
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq1627
       grind)
    | (have r₁ := eq13 y y
       have r₂ := eq1627
       grind)
    | exact resolve eq13 eq1627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1627
  have eq1697 : (σ y) = (k (σ y) (σ y)) ∨ y = (M.op y y) := by grind
  clear eq1682
  have eq1716 : (τ (σ y)) = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq1697 eq92
    | exact resolve eq92 eq1697
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92 eq1697
  have eq1720 : y = (k y y) ∨ y = (M.op y y) := by
    first
    | exact superpose eq29 eq1716
    | exact resolve eq1716 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq1716
  have eq1761 : y = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq82 y y
       have i₂ := eq1720
       grind)
    | exact superpose eq1720 eq82
    | (have j0 := eq82 x y
       grind)
    | exact resolve eq82 eq1720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1720
  have eq1762 : y = (M.op y y) := by grind
  clear eq1761
  have eq1766 : y ≠ y ∨ y = (k y y) := by
    first
    | (have i₁ := eq13 y y
       have i₂ := eq1762
       grind)
    | exact superpose eq1762 eq13
    | (have r₁ := eq13 y y
       have r₂ := eq1762
       grind)
    | exact resolve eq13 eq1762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1773 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq56 y y
       have i₂ := eq1762
       grind)
    | exact superpose eq1762 eq56
    | exact resolve eq56 eq1762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1777 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq403 X0 y y
       have i₂ := eq1762
       grind)
    | exact superpose eq1762 eq403
    | exact resolve eq403 eq1762
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq403 eq1762
  have eq1780 : y = (k y y) := by grind
  clear eq1766
  have eq1786 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq209 eq1773
    | exact resolve eq1773 eq209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209 eq1773
  have eq1793 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq1786
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1786
    | exact resolve eq1786 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1786
  have eq1856 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq80
       have i₂ := eq1780
       grind)
    | exact superpose eq1780 eq80
    | exact resolve eq80 eq1780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq1780
  have eq1860 : (σ y) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq1856
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1856
    | exact resolve eq1856 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq1856
  have eq1894 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1793 eq311
    | exact resolve eq311 eq1793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq311
  have eq1932 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq1860 eq82
    | (have j0 := eq82 x (σ y)
       grind)
    | exact resolve eq82 eq1860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1860
  have eq1933 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq1932
  have eq1941 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq1894 eq13
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq1894
       grind)
    | exact resolve eq13 eq1894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1894
  have eq1955 : (M.op x y) = (k (M.op x y) (M.op x y)) := by grind
  clear eq1941
  have eq1971 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq1933 eq57
    | exact resolve eq57 eq1933
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1933
  have eq1984 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq220 eq1971
    | exact resolve eq1971 eq220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq220 eq1971
  have eq1992 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq26 eq1984
    | exact resolve eq1984 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq1984
  have eq2003 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1955 eq132
    | exact resolve eq132 eq1955
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132 eq1955
  have eq2007 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq2003
    | exact resolve eq2003 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2003
  have eq2122 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2007 eq82
    | (have j0 := eq82 x (σ (M.op x y))
       grind)
    | exact resolve eq82 eq2007
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq2007
  have eq2123 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq2122
  have eq2208 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq2123 eq881
    | exact resolve eq881 eq2123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2214 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq2123 eq2208
    | exact resolve eq2208 eq2123
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2123 eq2208
  have eq2560 : (σ (M.op x y)) = (M.op (σ (M.op x y)) y) := by
    first
    | exact superpose eq2214 eq1777
    | exact resolve eq1777 eq2214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2214
  have eq2561 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq1992 eq1777
    | exact resolve eq1777 eq1992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1992
  have eq10175 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1414 (τ X0)
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq1414
    | (have j0 := eq1414 (τ X0)
       grind)
    | exact resolve eq1414 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414
  have eq10196 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10175 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10175
    | (have j0 := eq10175 X0
       grind)
    | exact resolve eq10175 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10175
  have eq10204 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10196 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10196
    | (have j0 := eq10196 X0
       grind)
    | exact resolve eq10196 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10196
  have eq18804 : ∀ X0 X1 : G, (M.op (σ (k X0 X1)) (σ X1)) = (M.op (σ X0) y) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | exact superpose eq1777 eq1424
    | (have j0 := eq1424 X0 X1
       grind)
    | exact resolve eq1424 eq1777
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1424 eq1777
  have eq18944 : ∀ X0 X1 : G, (M.op (σ X0) y) = (σ (k (k X0 X1) X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq98 (k X0 X1) X1
       have i₂ := eq18804 X0 X1
       grind)
    | exact superpose eq18804 eq98
    | (have j0 := eq98 X0 X1
       have j1 := eq18804 X0 X1
       grind)
    | exact resolve eq98 eq18804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq18804
  have eq18974 : ∀ X0 X1 : G, (M.op (σ X0) y) = (σ (k (k X0 X1) X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq18944 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18944
  have eq95379 : ∀ X0 : G, (M.op (σ x) y) = (σ (k (τ (k (σ x) X0)) (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq18974 x (τ X0)
       have i₂ := eq1538 X0
       grind)
    | exact superpose eq1538 eq18974
    | (have j0 := eq18974 X0 (τ X0)
       grind)
    | exact resolve eq18974 eq1538
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1538
  have eq95677 : ∀ X0 : G, (M.op (σ x) y) = (k (k (σ x) X0) (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq95379 X0
       have i₂ := eq34 (k sF2 X0) (τ X0)
       grind)
    | exact superpose eq34 eq95379
    | (have j0 := eq95379 X0
       grind)
    | exact resolve eq95379 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95379
  have eq95858 : ∀ X0 : G, (M.op (σ x) y) = (k (k (σ x) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq95677 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq95677
    | (have j0 := eq95677 X0
       grind)
    | exact resolve eq95677 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95677
  have eq95971 : ∀ X0 : G, (M.op (σ x) y) = (k (k (σ x) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq95858 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq95858
    | (have j0 := eq95858 X0
       grind)
    | exact resolve eq95858 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95858
  have eq96009 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (k (σ x) X0) X0) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | exact superpose eq2561 eq95971
    | (have j0 := eq95971 X0
       grind)
    | exact resolve eq95971 eq2561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95971
  have eq96031 : ∀ X0 : G, (M.op (σ x) (σ y)) = (k (k (σ x) X0) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq96009 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq96009
    | (have j0 := eq96009 X0
       grind)
    | exact resolve eq96009 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96009
  have eq696327 : ∀ X0 X1 : G, (M.op (σ (τ X0)) y) = (σ (k (τ (k X0 X1)) (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18974 (τ X0) (τ X1)
       have i₂ := eq1442 X1 X0
       grind)
    | exact superpose eq1442 eq18974
    | (have j0 := eq18974 X0 (τ X1)
       grind)
    | exact resolve eq18974 eq1442
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1442 eq18974
  have eq696381 : ∀ X0 X1 : G, (M.op (σ (τ X0)) y) = (k (k X0 X1) (σ (τ X1))) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq696327 X0 X1
       have i₂ := eq34 (k X0 X1) (τ X1)
       grind)
    | exact superpose eq34 eq696327
    | (have j0 := eq696327 X0 X1
       grind)
    | exact resolve eq696327 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34 eq696327
  have eq696565 : ∀ X0 X1 : G, (M.op (σ (τ X0)) y) = (k (k X0 X1) X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq696381 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq696381
    | (have j0 := eq696381 X0 X1
       grind)
    | exact resolve eq696381 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696381
  have eq696739 : ∀ X0 X1 : G, (M.op X0 y) = (k (k X0 X1) X1) ∨ (σ (τ X1)) = (M.op (σ (τ X1)) (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq696565 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq696565
    | (have j0 := eq696565 X0 X1
       grind)
    | exact resolve eq696565 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696565
  have eq696853 : ∀ X0 X1 : G, (M.op X0 y) = (k (k X0 X1) X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq696739 X0 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq696739
    | (have j0 := eq696739 X0 X1
       grind)
    | exact resolve eq696739 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq696739
  have eq2169458 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq150
       have i₂ := eq696853 x x
       grind)
    | exact superpose eq696853 eq150
    | (have j1 := eq696853 x x
       grind)
    | exact resolve eq150 eq696853
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150 eq696853
  have eq2169700 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2169458
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2169458
    | exact resolve eq2169458 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2169458
  have eq2171969 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq2169700
    | exact resolve eq2169700 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2169700
  have eq2173397 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2171969 eq96031
    | (have j0 := eq96031 (σ x)
       grind)
    | exact resolve eq96031 eq2171969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96031 eq2171969
  have eq2173486 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq2173397
       have r₂ := eq27
       grind)
    | exact resolve eq2173397 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2173397
  have eq2173512 : (σ x) ≠ (σ x) ∨ (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2173486 eq13
    | (have r₁ := eq13 (σ x) (σ x)
       have r₂ := eq2173486
       grind)
    | (have r₁ := eq13 x x
       have r₂ := eq2173486
       grind)
    | exact resolve eq13 eq2173486
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2173486
  have eq2173568 : (σ x) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq2173512
  have eq2173663 : (τ (σ x)) = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2173568 eq49
    | exact resolve eq49 eq2173568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49 eq2173568
  have eq2173803 : x = (k x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq2173663
    | exact resolve eq2173663 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2173663
  have eq2173807 : x = (M.op x x) := by
    first
    | (have j1 := eq10204 x
       grind)
    | (have r₁ := eq2173803
       have r₂ := eq10204 x
       grind)
    | exact resolve eq2173803 eq10204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10204 eq2173803
  have eq2173825 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq881 x x
       have i₂ := eq2173807
       grind)
    | exact superpose eq2173807 eq881
    | exact resolve eq881 eq2173807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq881
  have eq2173899 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq1793 eq2173825
    | exact resolve eq2173825 eq1793
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1793 eq2173825
  have eq2173930 : x = (M.op x y) := by
    first
    | (have i₁ := eq2173899
       have i₂ := eq2173807
       grind)
    | exact superpose eq2173807 eq2173899
    | exact resolve eq2173899 eq2173807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2173807 eq2173899
  have eq2173967 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2173930 eq20
    | exact resolve eq20 eq2173930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2173930
  have eq2175223 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2173967
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2173967
    | exact resolve eq2173967 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2173967
  have eq2175310 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) y) := by
    first
    | exact superpose eq2175223 eq2561
    | exact resolve eq2561 eq2175223
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2561 eq2175223
  have eq2176002 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq2560 eq2175310
    | exact resolve eq2175310 eq2560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2560 eq2175310
  have eq2176139 : False := by grind
  exact eq2176139

/-- `Equation4521`: `x ◇ (y ◇ z) = (x ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then X else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyy_x_pyy_pxy_Equation4521 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law4521 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4521.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X0 X3) X3) := by
    intro X0 X1 X2 X3
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
  have eq53 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq16
    | exact resolve eq16 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : ∀ X0 X1 X4 : G, (M.op (M.op X0 X1) X1) = (M.op (M.op X0 X4) X4) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq14 X0 x x X4
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op X0 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X1) (M.op X4 X5)) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq14 X0 X2 X3 (M.op X4 X5)
       have i₂ := eq14 X0 X4 X5 X1
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (M.op x (M.op X0 X1)) = (M.op (M.op x y) y) := by
    intro X0 X1
    first
    | (have i₁ := eq14 x X0 X1 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq14
    | (have j0 := eq14 x X0 X1 y
       grind)
    | exact resolve eq14 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66 : ∀ X0 X1 : G, (M.op (σ x) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 (σ x) X0 X1 (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq14 X0 X1 X2 x
       have i₂ := eq14 X0 X3 X4 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op (M.op (M.op X0 X1) X2) X2) ∨ (k X3 (M.op X0 X1)) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 (M.op X0 X1)
       have i₂ := eq14 (M.op X0 X1) X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X3 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq79 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq104 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq16
    | exact resolve eq16 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq114 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq153 : (σ (k (k x x) x)) = (k (k (σ x) (σ x)) (σ x)) := by
    first
    | (have i₁ := eq39 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq39
    | exact resolve eq39 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq204 : (M.op (M.op x y) y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq65 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq65
    | (have j0 := eq65 x y
       grind)
    | exact resolve eq65 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq218 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | (have i₁ := eq66 x y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq66
    | (have j0 := eq66 x y
       grind)
    | exact resolve eq66 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq256 : ∀ X0 X1 : G, (σ (k (k (τ X0) X1) x)) = (k (k X0 (σ X1)) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq39 (k (τ X0) X1)
       have i₂ := eq34 X0 X1
       grind)
    | exact superpose eq34 eq39
    | exact resolve eq39 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq312 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq16
    | exact resolve eq16 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq344 : ∀ X0 : G, (M.op (M.op x y) y) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | (have i₁ := eq61 x X0 y
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq61
    | (have j0 := eq61 x y X0
       grind)
    | exact resolve eq61 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq373 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op (M.op x X0) X0) := by
    intro X0
    first
    | exact superpose eq204 eq344
    | exact resolve eq344 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq344
  have eq387 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq67 X0 x y X1 X2
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq67
    | (have j0 := eq67 X0 X1 X2 x y
       grind)
    | exact resolve eq67 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq458 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq114 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq114
    | (have j0 := eq114 (σ X0)
       grind)
    | exact resolve eq114 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq729 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X1) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq387 X0 x x
       have i₂ := eq14 X0 x x X1
       grind)
    | exact superpose eq14 eq387
    | (have j1 := eq14 X0 x y X1
       grind)
    | exact resolve eq387 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq796 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X2 X3)) = (M.op (M.op (M.op X0 X1) X1) (M.op x y)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq63 X0 X1 X2 X3 x x
       have i₂ := eq387 (M.op (M.op X0 X1) X1) x x
       grind)
    | (have i₁ := eq63 X0 X1 X2 X3 x y
       have i₂ := eq387 (M.op (M.op X0 X1) X1) X1 X2
       grind)
    | exact superpose eq387 eq63
    | (have j0 := eq63 X0 X1 X2 X3 x y
       grind)
    | exact resolve eq63 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq797 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op (M.op (M.op X0 X1) X1) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq796 X0 X1 x x
       have i₂ := eq387 X0 x x
       grind)
    | (have i₁ := eq796 X0 X1 x y
       have i₂ := eq387 X0 X1 x
       grind)
    | exact superpose eq387 eq796
    | (have j0 := eq796 X0 X1 x y
       grind)
    | exact resolve eq796 eq387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq796
  have eq1172 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) ≠ (M.op X0 (M.op x y)) ∨ (k X1 (M.op X0 (M.op x y))) = X1 := by
    intro X0 X1
    first
    | exact superpose eq797 eq69
    | (have j0 := eq69 X0 (M.op x y) x X1
       grind)
    | (have r₁ := eq69 X0 (M.op x y) (M.op x y) x
       have r₂ := eq797 X0 (M.op x y)
       grind)
    | exact resolve eq69 eq797
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq797
  have eq1180 : ∀ X0 X1 : G, (k X1 (M.op X0 (M.op x y))) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1172 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1172
  have eq1235 : ∀ X0 X1 : G, (σ (τ X0)) = (k X0 (σ (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq1180 eq34
    | exact resolve eq34 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1238 : ∀ X0 X1 : G, (k X0 (σ (M.op X1 (M.op x y)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1235 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1235
    | exact resolve eq1235 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1235
  have eq1273 : ∀ X0 : G, (σ (M.op X0 (M.op x y))) = (M.op (σ (M.op X0 (M.op x y))) (σ (M.op X0 (M.op x y)))) ∨ (σ (M.op X0 (M.op x y))) = (M.op (σ (M.op X0 (M.op x y))) (σ (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq1238 eq114
    | (have j0 := eq114 (σ (M.op X0 (M.op x y)))
       grind)
    | exact resolve eq114 eq1238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1238
  have eq1276 : ∀ X0 : G, (σ (M.op X0 (M.op x y))) = (M.op (σ (M.op X0 (M.op x y))) (σ (M.op X0 (M.op x y)))) := by
    intro X0
    first
    | (have j0 := eq1273 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1273
  have eq1495 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq79 X1 X0
       grind)
    | (have i₁ := eq12 (σ X1) (σ X1)
       have i₂ := eq79 X0 X1
       grind)
    | exact superpose eq79 eq12
    | (have j0 := eq12 (σ X0) (σ X0)
       have j1 := eq79 X1 X0
       grind)
    | (have r₁ := eq12 (σ X1) (σ X1)
       have r₂ := eq79 X1 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq79 X0 X1
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1530 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq1533 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) ≠ (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1495 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1495
  have eq1534 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (k (σ X1) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1533 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533
  have eq1543 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1534 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq1534
    | (have j0 := eq1534 X0 X1
       grind)
    | exact resolve eq1534 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1534
  have eq1848 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | exact superpose eq1180 eq312
    | exact resolve eq312 eq1180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq312 eq1180
  have eq1872 : ∀ X0 X1 : G, (k X0 (τ (M.op X1 (M.op x y)))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq1848 X0 X1
       have i₂ := eq16 X0
       grind)
    | exact superpose eq16 eq1848
    | exact resolve eq1848 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1848
  have eq3315 : ∀ X0 : G, (k (k X0 (σ (τ X0))) (σ x)) = (σ (k (M.op (τ X0) (τ X0)) x)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq256 X0 (τ X0)
       have i₂ := eq114 (τ X0)
       grind)
    | exact superpose eq114 eq256
    | (have j1 := eq114 (τ X0)
       grind)
    | exact resolve eq256 eq114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq256
  have eq3367 : ∀ X0 : G, (σ (k (M.op (τ X0) (τ X0)) x)) = (k (k X0 X0) (σ x)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq3315 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq3315
    | (have j0 := eq3315 X0
       grind)
    | exact resolve eq3315 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3315
  have eq10770 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq458 X0
       grind)
    | exact superpose eq458 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq458 X0
       grind)
    | (have r₁ := eq13 X0 (σ X0)
       have r₂ := eq458 X0
       grind)
    | exact resolve eq13 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10775 : ∀ X0 X1 : G, (M.op (σ (k X0 X0)) (σ X0)) = (M.op (M.op (σ X0) X1) X1) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq61 (σ X0) X1 (σ X0)
       have i₂ := eq458 X0
       grind)
    | exact superpose eq458 eq61
    | (have j1 := eq458 X0
       grind)
    | exact resolve eq61 eq458
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq458
  have eq10802 : ∀ X0 : G, (M.op (σ X0) (M.op x y)) = (M.op (σ (k X0 X0)) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10775 X0 x
       have i₂ := eq729 (σ X0) x
       grind)
    | exact superpose eq729 eq10775
    | (have j0 := eq10775 X0 x
       grind)
    | exact resolve eq10775 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10775
  have eq10806 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (k X1 (σ X0)) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq10770 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq10770 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq10770 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10770
  have eq13412 : ∀ X0 X1 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10806 (τ X0) X1
       have i₂ := eq34 X0 (τ X0)
       grind)
    | exact superpose eq34 eq10806
    | (have j0 := eq10806 (τ X0) X1
       grind)
    | exact resolve eq10806 eq34
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq13444 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 (σ (τ X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13412 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq13412
    | (have j0 := eq13412 X0 X1
       grind)
    | exact resolve eq13412 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13412
  have eq13461 : ∀ X0 X1 : G, (k X0 X0) ≠ X0 ∨ (k X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13444 X0 X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq13444
    | (have j0 := eq13444 X0 X1
       grind)
    | exact resolve eq13444 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13444
  have eq19388 : ∀ X0 : G, (M.op (σ (M.op X0 (M.op x y))) (σ (M.op X0 (M.op x y)))) = (M.op (σ (M.op X0 (M.op x y))) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1276 eq729
    | exact resolve eq729 eq1276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19402 : ∀ X0 : G, (σ (M.op X0 (M.op x y))) = (M.op (σ (M.op X0 (M.op x y))) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1276 eq19388
    | exact resolve eq19388 eq1276
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19388
  have eq28362 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1543 X0 X1
       have j1 := eq1530 X1 X0
       grind)
    | (have r₁ := eq1543 X1 X0
       have r₂ := eq1530 X0 X1
       grind)
    | (have r₁ := eq1543 X1 X1
       have r₂ := eq1530 X1 X1
       grind)
    | exact resolve eq1543 eq1530
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1530 eq1543
  have eq28461 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28362 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq28362
    | exact resolve eq28362 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28545 : ∀ X0 : G, (σ (k X0 y)) = (M.op (σ X0) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq28362 y X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq28362
    | (have j0 := eq28362 y X0
       grind)
    | exact resolve eq28362 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq28667 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq28461 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq28461
    | (have j0 := eq28461 X0 X1
       grind)
    | exact resolve eq28461 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq28461
  have eq29362 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq28545 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq28545
    | (have j0 := eq28545 x
       grind)
    | exact resolve eq28545 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28545
  have eq29441 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq29362
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq29362
    | exact resolve eq29362 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29362
  have eq29459 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq29441
    | exact resolve eq29441 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29441
  have eq30043 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28667 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq28667
    | (have j0 := eq28667 X1 X1
       grind)
    | exact resolve eq28667 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28667
  have eq30795 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq44
       have i₂ := eq30043 x y
       grind)
    | exact superpose eq30043 eq44
    | (have j1 := eq30043 x y
       grind)
    | exact resolve eq44 eq30043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq31054 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq30795
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq30795
    | exact resolve eq30795 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30795
  have eq31117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq20 eq31054
    | exact resolve eq31054 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31054
  have eq31178 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | exact superpose eq31117 eq29459
    | exact resolve eq29459 eq31117
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29459 eq31117
  have eq31185 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq31178
       have r₂ := eq27
       grind)
    | exact resolve eq31178 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31178
  have eq31207 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 ∨ y = (M.op y y) := by
    intro X0
    first
    | exact superpose eq31185 eq13
    | (have j0 := eq13 X0 (σ y)
       grind)
    | (have r₁ := eq13 X0 (σ y)
       have r₂ := eq31185
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq31185
       grind)
    | exact resolve eq13 eq31185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31185
  have eq31228 : ∀ X0 : G, y = (M.op y y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq31207 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31207
  have eq31242 : ∀ X0 X1 : G, y ≠ y ∨ (k X0 y) = X0 ∨ (k X1 (σ y)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq31228 X1
       grind)
    | exact superpose eq31228 eq13
    | (have j0 := eq13 X0 y
       have j1 := eq31228 X1
       grind)
    | (have r₁ := eq13 X0 y
       have r₂ := eq31228 X0
       grind)
    | exact resolve eq13 eq31228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31228
  have eq31262 : ∀ X0 X1 : G, (k X1 (σ y)) = X1 ∨ (k X0 y) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31242 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31242
  have eq31432 : ∀ X0 : G, (τ (σ y)) = (k y y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | (have i₁ := eq104
       have i₂ := eq31262 (k sF3 sF3) x
       grind)
    | exact superpose eq31262 eq104
    | (have j1 := eq31262 X0 x
       grind)
    | exact resolve eq104 eq31262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq31262
  have eq31494 : ∀ X0 : G, y = (k y y) ∨ (k X0 y) = X0 := by
    intro X0
    first
    | exact superpose eq29 eq31432
    | (have j0 := eq31432 y
       grind)
    | exact resolve eq31432 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq31432
  have eq31542 : ∀ X0 : G, (k X0 y) = X0 := by
    intro X0
    first
    | (have j0 := eq31494 X0
       have j1 := eq13461 y X0
       grind)
    | (have r₁ := eq31494 X0
       have r₂ := eq13461 y x
       grind)
    | (have r₁ := eq31494 y
       have r₂ := eq13461 y x
       grind)
    | exact resolve eq31494 eq13461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13461 eq31494
  have eq31598 : ∀ X0 : G, (σ y) ≠ (σ y) ∨ (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq10806 y X0
       have i₂ := eq31542 y
       grind)
    | exact superpose eq31542 eq10806
    | (have j0 := eq10806 y X0
       grind)
    | exact resolve eq10806 eq31542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10806
  have eq31599 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq114 y
       have i₂ := eq31542 y
       grind)
    | exact superpose eq31542 eq114
    | (have j0 := eq114 y
       grind)
    | exact resolve eq114 eq31542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31620 : y = (M.op y y) := by grind
  clear eq31599
  have eq31621 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have j0 := eq31598 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31598
  have eq31642 : ∀ X0 : G, (k X0 (σ y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq31621 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq31621
    | (have j0 := eq31621 X0
       grind)
    | exact resolve eq31621 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq31621
  have eq31709 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq65 y y
       have i₂ := eq31620
       grind)
    | exact superpose eq31620 eq65
    | exact resolve eq65 eq31620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq31714 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq387 X0 y y
       have i₂ := eq31620
       grind)
    | exact superpose eq31620 eq387
    | exact resolve eq387 eq31620
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq387 eq31620
  have eq31736 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq204 eq31709
    | exact resolve eq31709 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204 eq31709
  have eq31742 : (M.op x y) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq31736
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31736
    | exact resolve eq31736 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31736
  have eq31804 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq31642 eq114
    | (have j0 := eq114 (σ y)
       grind)
    | exact resolve eq114 eq31642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31825 : (σ y) = (M.op (σ y) (σ y)) := by grind
  clear eq31804
  have eq32056 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq31742 eq1276
    | exact resolve eq1276 eq31742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1276
  have eq32086 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq31742 eq19402
    | exact resolve eq19402 eq31742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19402
  have eq32172 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq20 eq32086
    | exact resolve eq32086 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32086
  have eq32179 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq32056
    | exact resolve eq32056 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32056
  have eq32191 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq31825 eq66
    | exact resolve eq66 eq31825
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31825
  have eq32216 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq218 eq32191
    | exact resolve eq32191 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32191
  have eq32222 : (M.op (σ x) (σ y)) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq26 eq32216
    | exact resolve eq32216 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq32216
  have eq34876 : ∀ X0 : G, (k X0 (τ (M.op (σ x) (σ y)))) = X0 := by
    intro X0
    first
    | exact superpose eq32222 eq1872
    | exact resolve eq1872 eq32222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1872
  have eq55436 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq34876 eq114
    | (have j0 := eq114 (τ (M.op (σ x) (σ y)))
       grind)
    | exact resolve eq114 eq34876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114 eq34876
  have eq55470 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by grind
  clear eq55436
  have eq55668 : (σ (M.op x y)) = (M.op (σ (M.op x y)) y) := by
    first
    | exact superpose eq32172 eq31714
    | exact resolve eq31714 eq32172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32172
  have eq55669 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq32222 eq31714
    | exact resolve eq31714 eq32222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56068 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq55668 eq66
    | exact resolve eq66 eq55668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66 eq55668
  have eq56092 : (M.op (σ x) (σ (M.op x y))) = (M.op (σ x) (M.op x y)) := by
    first
    | exact superpose eq218 eq56068
    | exact resolve eq56068 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq56068
  have eq56102 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq32222 eq56092
    | exact resolve eq56092 eq32222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56092
  have eq107358 : (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) (M.op x y)) := by
    first
    | exact superpose eq55470 eq729
    | exact resolve eq729 eq55470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107385 : (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) = (M.op (τ (M.op (σ x) (σ y))) y) := by
    first
    | exact superpose eq31714 eq107358
    | exact resolve eq107358 eq31714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107358
  have eq107403 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) y) := by
    first
    | exact superpose eq55470 eq107385
    | exact resolve eq107385 eq55470
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55470 eq107385
  have eq213279 : ∀ X0 : G, (M.op (σ (k X0 X0)) (σ X0)) = (M.op (σ X0) y) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | exact superpose eq31714 eq10802
    | (have j0 := eq10802 X0
       grind)
    | exact resolve eq10802 eq31714
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10802 eq31714
  have eq215371 : ∀ X0 : G, (M.op (σ X0) y) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq28362 X0 (k X0 X0)
       have i₂ := eq213279 X0
       grind)
    | exact superpose eq213279 eq28362
    | (have j0 := eq28362 X0 x
       have j1 := eq213279 X0
       grind)
    | exact resolve eq28362 eq213279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28362 eq213279
  have eq215432 : ∀ X0 : G, (M.op (σ X0) y) = (σ (k (k X0 X0) X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq215371 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215371
  have eq248626 : (k (k (k (σ x) (σ y)) (k (σ x) (σ y))) (σ x)) = (σ (k (M.op (k x y) (k x y)) x)) ∨ (k x y) = (M.op (k x y) (k x y)) := by
    first
    | exact superpose eq53 eq3367
    | exact resolve eq3367 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq3367
  have eq248842 : (σ (k (M.op x x) x)) = (k (k (k (σ x) (σ y)) (k (σ x) (σ y))) (σ x)) ∨ (k x y) = (M.op (k x y) (k x y)) := by
    first
    | (have i₁ := eq248626
       have i₂ := eq31542 x
       grind)
    | exact superpose eq31542 eq248626
    | exact resolve eq248626 eq31542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248626
  have eq248928 : (k (k (σ x) (σ x)) (σ x)) = (σ (k (M.op x x) x)) ∨ (k x y) = (M.op (k x y) (k x y)) := by
    first
    | exact superpose eq31642 eq248842
    | exact resolve eq248842 eq31642
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31642 eq248842
  have eq248986 : (k (k (σ x) (σ x)) (σ x)) = (σ (k (M.op x x) x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq248928
       have i₂ := eq31542 x
       grind)
    | exact superpose eq31542 eq248928
    | exact resolve eq248928 eq31542
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31542 eq248928
  have eq2050236 : (k (k (σ x) (σ x)) (σ x)) = (σ (M.op (M.op x x) x)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq248986
       have i₂ := eq30043 (M.op x x) x
       grind)
    | exact superpose eq30043 eq248986
    | (have j1 := eq30043 x x
       grind)
    | exact resolve eq248986 eq30043
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30043 eq248986
  have eq2050577 : (k (k (σ x) (σ x)) (σ x)) = (σ (M.op (M.op x x) x)) ∨ x = (M.op x x) := by grind
  clear eq2050236
  have eq2050621 : (σ (M.op x (M.op x y))) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq2050577
       have i₂ := eq373 x
       grind)
    | exact superpose eq373 eq2050577
    | exact resolve eq2050577 eq373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq373 eq2050577
  have eq2050654 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq31742 eq2050621
    | exact resolve eq2050621 eq31742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2050621
  have eq2050664 : (σ (M.op x y)) = (k (k (σ x) (σ x)) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq2050654
    | exact resolve eq2050654 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2050654
  have eq2317469 : (k (k (σ x) (σ x)) (σ x)) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq153
       have i₂ := eq215432 x
       grind)
    | exact superpose eq215432 eq153
    | (have j1 := eq215432 x
       grind)
    | exact resolve eq153 eq215432
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq215432
  have eq2318150 : (k (k (σ x) (σ x)) (σ x)) = (M.op (σ x) y) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2317469
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2317469
    | exact resolve eq2317469 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2317469
  have eq2319976 : (M.op (σ x) (σ y)) = (k (k (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq55669 eq2318150
    | exact resolve eq2318150 eq55669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55669 eq2318150
  have eq2321513 : (M.op (σ x) (σ y)) = (k (k (σ x) (σ x)) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2319976
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2319976
    | exact resolve eq2319976 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2319976
  have eq2873484 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq2321513 eq2050664
    | exact resolve eq2050664 eq2321513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2050664 eq2321513
  have eq2873615 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq2873484
       have r₂ := eq27
       grind)
    | exact resolve eq2873484 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2873484
  have eq2873640 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op x y)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2873615 eq729
    | exact resolve eq729 eq2873615
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2873712 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq32222 eq2873640
    | exact resolve eq2873640 eq32222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32222 eq2873640
  have eq2882362 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2873712 eq2873615
    | exact resolve eq2873615 eq2873712
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2873615 eq2873712
  have eq2882437 : x = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq2882362
  have eq2882521 : (M.op x x) = (M.op x (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq729 x x
       have i₂ := eq2882437
       grind)
    | exact superpose eq2882437 eq729
    | exact resolve eq729 eq2882437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq729
  have eq2882583 : (M.op x y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31742 eq2882521
    | exact resolve eq2882521 eq31742
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31742 eq2882521
  have eq2884222 : x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq2882437
       have i₂ := eq2882583
       grind)
    | exact superpose eq2882583 eq2882437
    | exact resolve eq2882437 eq2882583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2882437 eq2882583
  have eq2884288 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq2884222
  have eq2884435 : (τ (σ x)) = (M.op (τ (σ x)) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq2884288 eq107403
    | exact resolve eq107403 eq2884288
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107403 eq2884288
  have eq2885100 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq2884435
    | exact resolve eq2884435 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq2884435
  have eq2885125 : x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq2885100
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq2885100
    | exact resolve eq2885100 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq2885100
  have eq2885126 : x = (M.op x y) := by grind
  clear eq2885125
  have eq2886258 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq2885126 eq20
    | exact resolve eq20 eq2885126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq2885126
  have eq2887045 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq2886258
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2886258
    | exact resolve eq2886258 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2886258
  have eq2887264 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2887045 eq56102
    | exact resolve eq56102 eq2887045
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56102 eq2887045
  have eq2887666 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32179 eq2887264
    | exact resolve eq2887264 eq32179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32179 eq2887264
  have eq2887813 : False := by grind
  exact eq2887813

/-- `Equation4521`: `x ◇ (y ◇ z) = (x ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,Y) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyy_pxx_pxy_pyx_Equation4521 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4521 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4521.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) ≠ (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq18 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq14 (σ y) (σ x)
       grind)
    | exact superpose eq14 eq16
    | (have j1 := eq14 (σ y) (σ x)
       grind)
    | (have r₁ := eq16
       have r₂ := eq14 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq14 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19 : (σ (M.op x y)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13 (σ x) (σ y)
       grind)
    | exact superpose eq13 eq16
    | (have j1 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq16
       have r₂ := eq13 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq13 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq19
    | exact resolve eq19 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq21 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq18
    | exact resolve eq18 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq22 : (M.op (σ y) (σ y)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by grind
  clear eq20
  have eq23 : (M.op (σ y) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by grind
  clear eq21
  have eq24 : (M.op (σ y) (σ y)) ≠ (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq22
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq22
    | exact resolve eq22 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq25 : (M.op (σ y) (σ y)) = (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq23
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq23
    | exact resolve eq23 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23
  have eq26 : (σ (k x x)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by grind
  clear eq24
  have eq27 : (σ (k x x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by grind
  clear eq25
  have eq28 : (σ (k x x)) ≠ (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq26
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq26
    | exact resolve eq26 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq29 : (σ (k x x)) = (σ (k y y)) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq27
       have i₂ := eq15 y y
       grind)
    | exact superpose eq15 eq27
    | exact resolve eq27 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq33 : (k y y) = (τ (σ (k x x))) ∨ (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq10 (k y y)
       have i₂ := eq29
       grind)
    | exact superpose eq29 eq10
    | exact resolve eq10 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29
  have eq36 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq33
       have i₂ := eq10 (k x x)
       grind)
    | exact superpose eq10 eq33
    | exact resolve eq33 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33
  have eq39 : (σ (k y x)) ≠ (σ (k y x)) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq36
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq36
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq36
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq36
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq36 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq41 : (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ (M.op y y) = (M.op x x) ∨ x = y := by grind
  clear eq39
  have eq43 : (k x x) = (M.op y y) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq41
  have eq45 : (k x x) = (k y y) ∨ (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq43
  have eq46 : (k x x) = (k y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq45
  have eq47 : (σ (k x x)) ≠ (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq28
       have i₂ := eq46
       grind)
    | exact superpose eq46 eq28
    | exact resolve eq28 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq48 : (σ (k x x)) ≠ (σ (k x x)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq47
  have eq49 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq48
  have eq51 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op y y) ≠ (M.op x x) ∨ x = y := by
    first
    | (have i₁ := eq49
       have i₂ := eq13 x y
       grind)
    | exact superpose eq13 eq49
    | (have j1 := eq13 y x
       grind)
    | (have r₁ := eq49
       have r₂ := eq13 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq49
       have r₂ := eq13 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq49 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq52 : (σ (k x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op y y) ≠ (M.op x x) := by grind
  clear eq51
  have eq53 : (σ x) = (σ y) ∨ x = y ∨ (M.op y y) ≠ (M.op x x) := by grind
  clear eq52
  have eq55 : (k x x) ≠ (M.op y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq53
  have eq57 : (k x x) ≠ (k y y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq55
  have eq59 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq57
       have r₂ := eq46
       grind)
    | exact resolve eq57 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq57
  have eq63 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq59
       grind)
    | exact superpose eq59 eq10
    | exact resolve eq10 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq64 : x = y ∨ x = y := by
    first
    | (have i₁ := eq63
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq63
    | exact resolve eq63 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq65 : x = y := by grind
  clear eq64
  have eq70 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65
       grind)
    | exact superpose eq65 eq16
    | exact resolve eq16 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq71 : (M.op (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq70
  have eq72 : (k (σ x) (σ x)) ≠ (σ (k x x)) := by grind
  clear eq71
  have eq73 : False := by grind
  exact eq73

/-- `Equation4521`: `x ◇ (y ◇ z) = (x ◇ w) ◇ w`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation4521 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4521 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4521.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
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
  have eq74 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq97 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq97
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq97
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq97 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq110 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq104
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq104
    | exact resolve eq104 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq111 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq21 eq110
    | exact resolve eq110 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110
  have eq112 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have i₁ := eq111
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq111
    | exact resolve eq111 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq15999 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq112 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16000 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq15999
    | exact resolve eq15999 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15999
  have eq16011 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq16000
       have r₂ := eq28
       grind)
    | exact resolve eq16000 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16000
  have eq16015 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq27 eq16011
    | exact resolve eq16011 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16011
  have eq16017 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq16015 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq16015
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq16015
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq16015
       grind)
    | exact resolve eq12 eq16015
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16015
  have eq16040 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = y := by grind
  clear eq16017
  have eq16051 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | (have r₁ := eq16040
       have r₂ := eq27
       grind)
    | exact resolve eq16040 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16040
  have eq16306 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y x) ∨ x = y := by
    first
    | exact superpose eq16051 eq112
    | exact resolve eq112 eq16051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq16051
  have eq16315 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq16306
  have eq16318 : (M.op x y) = (M.op y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq16315
       have r₂ := eq28
       grind)
    | exact resolve eq16315 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16315
  have eq16320 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq16318
       grind)
    | exact superpose eq16318 eq12
    | (have j0 := eq12 x y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq16318
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq16318
       grind)
    | exact resolve eq12 eq16318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16318
  have eq16341 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ (M.op x y) = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq16320
  have eq16349 : (M.op x y) = (k y x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq16341
       have r₂ := eq19
       grind)
    | exact resolve eq16341 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16341
  have eq16352 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq16349
       grind)
    | exact superpose eq16349 eq97
    | exact resolve eq97 eq16349
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq16349
  have eq16368 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq16352
    | exact resolve eq16352 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16352
  have eq16403 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq16368 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq16368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16404 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq16403
  have eq16408 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq16404
    | exact resolve eq16404 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16404
  have eq16419 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq16408
       have r₂ := eq28
       grind)
    | exact resolve eq16408 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16408
  have eq16423 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq16419
    | exact resolve eq16419 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16419
  have eq16652 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16423 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq16423
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq16423
       grind)
    | exact resolve eq12 eq16423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16423
  have eq16675 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = y := by grind
  clear eq16652
  have eq16686 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq16675
       have r₂ := eq27
       grind)
    | exact resolve eq16675 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16675
  have eq16703 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq16686 eq16368
    | exact resolve eq16368 eq16686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16368 eq16686
  have eq16706 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq16703
  have eq16711 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq16706
       have r₂ := eq28
       grind)
    | exact resolve eq16706 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16706
  have eq16714 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq16711 eq30
    | exact resolve eq30 eq16711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq16711
  have eq16823 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq16714
    | exact resolve eq16714 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq16714
  have eq16824 : x = y := by grind
  clear eq16823
  have eq16843 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq16824
       grind)
    | exact superpose eq16824 eq19
    | exact resolve eq19 eq16824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq16844 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq16824
       grind)
    | exact superpose eq16824 eq25
    | exact resolve eq25 eq16824
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq16824
  have eq16946 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq16844
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq16844
    | exact resolve eq16844 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq16844
  have eq17218 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq16946 eq27
    | exact resolve eq27 eq16946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq16946
  have eq17445 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq17218 eq74
    | exact resolve eq74 eq17218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74 eq17218
  have eq17506 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq17445
       have i₂ := eq16843
       grind)
    | exact superpose eq16843 eq17445
    | exact resolve eq17445 eq16843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16843 eq17445
  have eq17520 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17506 eq15
    | exact resolve eq15 eq17506
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17506
  have eq17563 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq17520
    | exact resolve eq17520 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq17520
  have eq17574 : False := by grind
  exact eq17574

/-- `Equation4542`: `x ◇ (y ◇ z) = (z ◇ x) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then X else if m(X,Y) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_x_pyx_pxy_Equation4542 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law4542 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4542.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = M.op b a :=
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
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 X2)) = (M.op (M.op X2 X0) X2) := by
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
  have eq72 : ∀ X0 : G, (k X0 y) = (τ (k (σ X0) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq15 (k X0 y)
       have i₂ := eq40 X0
       grind)
    | exact superpose eq40 eq15
    | exact resolve eq15 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq152 : ∀ X0 : G, (k (τ X0) y) = (τ (k X0 (σ y))) := by
    intro X0
    first
    | (have i₁ := eq72 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq72
    | exact resolve eq72 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq174 : x ≠ (M.op x y) ∨ y = (k y x) := by
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
  have eq175 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X3) X2) = (M.op X3 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X3 (M.op X2 X0) X2
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X0) (M.op X3 X1)) = (M.op (M.op (M.op X0 X1) X0) X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X2 X0) X3 X1
       have i₂ := eq16 X1 X2 X0
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op y (M.op X0 x)) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq16 y X0 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 y X0 x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (M.op (σ y) (M.op X0 (σ x))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ y) X0 (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X2)) = (M.op X0 (M.op X3 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 X0 X1 X2
       have i₂ := eq16 X0 X3 X2
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq568 : ∀ X0 X1 X2 X3 X4 : G, (M.op X3 (M.op X0 (M.op X1 X2))) = (M.op X3 (M.op X4 X2)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq183 X3 X4 X2 (M.op X2 X0)
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq183
    | exact resolve eq183 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq569 : ∀ X0 X1 : G, (M.op X0 (M.op X1 y)) = (M.op X0 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq183 X0 X1 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq183
    | (have j0 := eq183 X0 X1 y x
       grind)
    | exact resolve eq183 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq571 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ y))) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq26 eq183
    | (have j0 := eq183 X0 X1 (σ y) (σ x)
       grind)
    | exact resolve eq183 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq602 : ∀ X0 : G, (M.op (M.op y X0) y) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq16 X0 x y
       have i₂ := eq569 X0 x
       grind)
    | (have i₁ := eq16 X0 x y
       have i₂ := eq569 X0 x
       grind)
    | exact superpose eq569 eq16
    | (have j0 := eq16 X0 x y
       grind)
    | exact resolve eq16 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq604 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op x y))) = (M.op X1 (M.op X3 (M.op X2 y))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq183 X1 X0 (M.op X2 y) X3
       have i₂ := eq569 X0 X2
       grind)
    | (have i₁ := eq183 X1 X3 (M.op x y) X0
       have i₂ := eq569 X3 X2
       grind)
    | exact superpose eq569 eq183
    | exact resolve eq183 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq611 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op x y))) = (M.op (M.op y X1) y) := by
    intro X0 X1
    first
    | (have i₁ := eq604 X0 X1 x x
       have i₂ := eq177 x x y X1
       grind)
    | exact superpose eq177 eq604
    | (have j1 := eq177 X0 x y X1
       grind)
    | exact resolve eq604 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq616 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op x y))) = (M.op X1 (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq611 X0 X1
       have i₂ := eq602 X1
       grind)
    | exact superpose eq602 eq611
    | exact resolve eq611 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611
  have eq626 : ∀ X0 : G, (M.op (M.op (σ y) X0) (σ y)) = (M.op X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq571 eq16
    | (have j0 := eq16 X0 (σ x) (σ y)
       grind)
    | exact resolve eq16 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq628 : ∀ X0 X1 X2 X3 : G, (M.op X1 (M.op X0 (M.op (σ x) (σ y)))) = (M.op X1 (M.op X3 (M.op X2 (σ y)))) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq571 eq183
    | exact resolve eq183 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq632 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 (σ y)) X1) (M.op (σ x) (σ y))) = (M.op X1 (M.op X2 (M.op X0 (σ y)))) := by
    intro X0 X1 X2
    first
    | exact superpose eq571 eq16
    | exact resolve eq16 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq633 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ y)) X1) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) X1) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq632 X1 x X0
       have i₂ := eq177 X0 X1 sF3 x
       grind)
    | exact superpose eq177 eq632
    | exact resolve eq632 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq632
  have eq635 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (σ x) (σ y)))) = (M.op (M.op (σ y) X1) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq628 X0 x X1 X0
       have i₂ := eq177 X0 X1 sF3 x
       grind)
    | exact superpose eq177 eq628
    | (have j1 := eq177 X0 (σ x) (σ y) X1
       grind)
    | exact resolve eq628 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq628
  have eq639 : ∀ X0 X1 : G, (M.op (M.op (M.op X0 (σ y)) X1) (M.op (σ x) (σ y))) = (M.op X1 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq626 eq633
    | exact resolve eq633 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq633
  have eq640 : ∀ X0 X1 : G, (M.op X1 (M.op X0 (M.op (σ x) (σ y)))) = (M.op X1 (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq626 eq635
    | exact resolve eq635 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq635
  have eq643 : ∀ X0 : G, (M.op (M.op (M.op x y) x) y) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq602 (M.op X0 x)
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq602
    | exact resolve eq602 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181
  have eq647 : ∀ X0 : G, (M.op (M.op X0 y) (M.op x y)) = (M.op (M.op y (M.op x y)) y) := by
    intro X0
    first
    | (have i₁ := eq602 (M.op X0 y)
       have i₂ := eq569 y X0
       grind)
    | (have i₁ := eq602 (M.op x y)
       have i₂ := eq569 y x
       grind)
    | exact superpose eq569 eq602
    | exact resolve eq602 eq569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq661 : ∀ X0 : G, (M.op (M.op X0 y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq647 X0
       have i₂ := eq602 sF0
       grind)
    | exact superpose eq602 eq647
    | exact resolve eq647 eq602
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq647
  have eq671 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op (M.op (M.op x y) X0) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq616 eq16
    | exact resolve eq16 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq685 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq182 eq626
    | exact resolve eq626 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq691 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ y) (M.op (σ x) (σ y))) (σ y)) := by
    intro X0
    first
    | exact superpose eq571 eq626
    | exact resolve eq626 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq703 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq626 eq691
    | exact resolve eq691 eq626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq691
  have eq756 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op y (M.op X0 (M.op x y))) := by
    intro X0
    first
    | exact superpose eq661 eq16
    | exact resolve eq16 eq661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq661
  have eq764 : (M.op y (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq616 eq756
    | exact resolve eq756 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616 eq756
  have eq769 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) y) := by
    first
    | exact superpose eq764 eq602
    | exact resolve eq602 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq602
  have eq831 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
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
  have eq834 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq874 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq942 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (σ y) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq703 eq16
    | exact resolve eq16 eq703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq703
  have eq954 : (M.op (σ y) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq640 eq942
    | exact resolve eq942 eq640
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq640 eq942
  have eq1173 : (M.op (M.op x y) (M.op x y)) ≠ (M.op (M.op x y) (M.op x y)) ∨ y = (k y (M.op (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq769 eq13
    | (have j0 := eq13 y (M.op (M.op x y) (M.op x y))
       grind)
    | (have r₁ := eq13 y (M.op (M.op x y) (M.op x y))
       have r₂ := eq769
       grind)
    | exact resolve eq13 eq769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq769
  have eq1178 : y = (k y (M.op (M.op x y) (M.op x y))) := by grind
  clear eq1173
  have eq1193 : (σ y) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq1178 eq36
    | exact resolve eq36 eq1178
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq1178
  have eq1195 : (σ y) = (k (σ y) (σ (M.op (M.op x y) (M.op x y)))) := by
    first
    | (have i₁ := eq1193
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1193
    | exact resolve eq1193 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193
  have eq1355 : ∀ X0 X1 : G, (M.op y (M.op X1 (M.op (M.op x y) x))) = (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op x y) x)) := by
    intro X0 X1
    first
    | exact superpose eq643 eq16
    | exact resolve eq16 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq643
  have eq1375 : ∀ X1 : G, (M.op y (M.op X1 (M.op (M.op x y) x))) = (M.op (M.op (M.op (M.op x y) x) (M.op x y)) x) := by
    intro X1
    first
    | (have i₁ := eq1355 x X1
       have i₂ := eq179 sF0 x (M.op x x) sF0
       grind)
    | exact superpose eq179 eq1355
    | exact resolve eq1355 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1355
  have eq1389 : ∀ X1 : G, (M.op y (M.op X1 (M.op (M.op x y) x))) = (M.op (M.op x (M.op x y)) x) := by
    intro X1
    first
    | exact superpose eq671 eq1375
    | exact resolve eq1375 eq671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq671 eq1375
  have eq1393 : (M.op (M.op x y) x) = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq1389 x
       have i₂ := eq177 x sF0 x y
       grind)
    | exact superpose eq177 eq1389
    | exact resolve eq1389 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1389
  have eq1395 : (M.op (M.op x y) x) = (M.op (M.op x (M.op x y)) x) := by
    first
    | (have i₁ := eq1393
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq1393
    | exact resolve eq1393 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1393
  have eq1427 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op x y) (M.op X0 x)) := by
    intro X0
    first
    | exact superpose eq1395 eq16
    | exact resolve eq16 eq1395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395
  have eq1888 : ∀ X0 X1 : G, (M.op (σ y) (M.op X1 (M.op (M.op (σ x) (σ y)) (σ x)))) = (M.op (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) (M.op (M.op (σ x) (σ y)) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq685 eq16
    | exact resolve eq16 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1895 : (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq685 eq639
    | exact resolve eq639 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639
  have eq1922 : ∀ X1 : G, (M.op (σ y) (M.op X1 (M.op (M.op (σ x) (σ y)) (σ x)))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op (σ x) (σ y))) (σ x)) := by
    intro X1
    first
    | (have i₁ := eq1888 x X1
       have i₂ := eq179 sF4 sF2 (M.op x sF2) sF4
       grind)
    | exact superpose eq179 eq1888
    | exact resolve eq1888 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq1888
  have eq1939 : ∀ X1 : G, (M.op (σ y) (M.op X1 (M.op (M.op (σ x) (σ y)) (σ x)))) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) (σ x)) := by
    intro X1
    first
    | exact superpose eq685 eq1922
    | exact resolve eq1922 eq685
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq685 eq1922
  have eq1945 : ∀ X1 : G, (M.op (σ y) (M.op X1 (M.op (M.op (σ x) (σ y)) (σ x)))) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    intro X1
    first
    | exact superpose eq1895 eq1939
    | exact resolve eq1939 eq1895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1895 eq1939
  have eq1947 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | (have i₁ := eq1945 x
       have i₂ := eq177 x sF4 sF2 sF3
       grind)
    | exact superpose eq177 eq1945
    | exact resolve eq1945 eq177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177 eq1945
  have eq1948 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) (σ x)) := by
    first
    | exact superpose eq26 eq1947
    | exact resolve eq1947 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1947
  have eq2283 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq831
       grind)
    | exact superpose eq831 eq40
    | exact resolve eq40 eq831
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2284 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq2283
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2283
    | exact resolve eq2283 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2283
  have eq2286 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq20 eq2284
    | exact resolve eq2284 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2284
  have eq2390 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (M.op X0 (σ x))) := by
    intro X0
    first
    | exact superpose eq1948 eq16
    | exact resolve eq16 eq1948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1948
  have eq3998 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq2286 eq834
    | exact resolve eq834 eq2286
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2286
  have eq4005 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq3998
       have r₂ := eq27
       grind)
    | exact resolve eq3998 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3998
  have eq4017 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq4005 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq4005
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq4005
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq4005
       grind)
    | exact resolve eq13 eq4005
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4005
  have eq4031 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by grind
  clear eq4017
  have eq4061 : (τ (σ x)) = (k (τ (σ x)) y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq4031 eq152
    | exact resolve eq152 eq4031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4031
  have eq4066 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ y = (M.op y x) := by
    first
    | exact superpose eq29 eq4061
    | exact resolve eq4061 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq4061
  have eq4069 : x = (k x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have j1 := eq13 x y
       grind)
    | (have r₁ := eq4066
       have r₂ := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq4066
       have r₂ := eq13 y x
       grind)
    | (have r₁ := eq4066
       have r₂ := eq13 x y
       grind)
    | exact resolve eq4066 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4066
  have eq4073 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq831
       have i₂ := eq4069
       grind)
    | exact superpose eq4069 eq831
    | exact resolve eq831 eq4069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq831
  have eq4075 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq40 x
       have i₂ := eq4069
       grind)
    | exact superpose eq4069 eq40
    | exact resolve eq40 eq4069
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq4069
  have eq4076 : y = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4073
  have eq4078 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq4075
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4075
    | exact resolve eq4075 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4075
  have eq4089 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq4076
       grind)
    | exact superpose eq4076 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq4076
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq4076
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq4076
       grind)
    | exact resolve eq12 eq4076
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4076
  have eq4105 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4089
  have eq4117 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4105
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4105
    | exact resolve eq4105 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4105
  have eq4118 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4117
  have eq4132 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4118
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq4118
    | exact resolve eq4118 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4118
  have eq4144 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4078 eq834
    | exact resolve eq834 eq4078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq834 eq4078
  have eq4148 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4144
  have eq4157 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq4132
       grind)
    | exact superpose eq4132 eq39
    | exact resolve eq39 eq4132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4132
  have eq4158 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4157
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq4157
    | exact resolve eq4157 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4157
  have eq4160 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq4158
    | exact resolve eq4158 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4158
  have eq4169 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4148 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq4148
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq4148
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq4148
       grind)
    | exact resolve eq12 eq4148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4148
  have eq4185 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq4169
  have eq4195 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq4185
    | exact resolve eq4185 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4185
  have eq4196 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq4195
  have eq4202 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq4196
    | exact resolve eq4196 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4196
  have eq4206 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4160 eq4202
    | exact resolve eq4202 eq4160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4160 eq4202
  have eq4208 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq4206
       have r₂ := eq27
       grind)
    | exact resolve eq4206 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4206
  have eq4210 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4208 eq27
    | exact resolve eq27 eq4208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4211 : (σ x) ≠ (σ x) ∨ (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4208 eq175
    | (have r₁ := eq175
       have r₂ := eq4208
       grind)
    | exact resolve eq175 eq4208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq4224 : (M.op (σ y) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4208 eq954
    | exact resolve eq954 eq4208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq954
  have eq4238 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq4211
  have eq5330 : (τ (σ y)) = (k (τ (σ y)) x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4238 eq141
    | exact resolve eq141 eq4238
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq4238
  have eq5331 : y = (k y x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq31 eq5330
    | exact resolve eq5330 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5330
  have eq5334 : y = (k y x) := by
    first
    | (have r₁ := eq5331
       have r₂ := eq174
       grind)
    | exact resolve eq5331 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq5331
  have eq5340 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq5334
       grind)
    | exact superpose eq5334 eq39
    | exact resolve eq39 eq5334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq5341 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq5340
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq5340
    | exact resolve eq5340 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5340
  have eq5391 : y ≠ y ∨ y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq874 y x
       have i₂ := eq5334
       grind)
    | exact superpose eq5334 eq874
    | (have j0 := eq874 y x
       grind)
    | (have r₁ := eq874 y x
       have r₂ := eq5334
       grind)
    | exact resolve eq874 eq5334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5399 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5341 eq874
    | (have j0 := eq874 (σ y) (σ x)
       grind)
    | (have r₁ := eq874 (σ y) (σ x)
       have r₂ := eq5341
       grind)
    | exact resolve eq874 eq5341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5402 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5399
  have eq5408 : y = (M.op y x) ∨ x = (M.op x y) := by grind
  clear eq5391
  have eq5414 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5402
    | exact resolve eq5402 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5402
  have eq5415 : y = (M.op y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5408
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5408
    | exact resolve eq5408 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5408
  have eq5424 : y ≠ y ∨ x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq5415
       grind)
    | exact superpose eq5415 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq5415
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq5415
       grind)
    | exact resolve eq12 eq5415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5444 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by grind
  clear eq5424
  have eq5460 : x = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5444
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5444
    | exact resolve eq5444 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5444
  have eq5461 : x = (M.op x y) ∨ (M.op x y) = (k y x) := by grind
  clear eq5460
  have eq5477 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5461
       have i₂ := eq5334
       grind)
    | exact superpose eq5334 eq5461
    | exact resolve eq5461 eq5334
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5334 eq5461
  have eq5487 : y = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5477
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq5477
    | exact resolve eq5477 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5477
  have eq5491 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq5487
       grind)
    | exact superpose eq5487 eq24
    | exact resolve eq24 eq5487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5513 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq5415
       have i₂ := eq5487
       grind)
    | exact superpose eq5487 eq5415
    | exact resolve eq5415 eq5487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5415 eq5487
  have eq5514 : (M.op x y) = (M.op (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq5513
  have eq5524 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq5491
    | exact resolve eq5491 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5491
  have eq5536 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5524 eq4210
    | exact resolve eq4210 eq5524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4210
  have eq5537 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq5536
  have eq5552 : (M.op (σ y) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5414 eq626
    | exact resolve eq626 eq5414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq626
  have eq5555 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5414 eq2390
    | exact resolve eq2390 eq5414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2390
  have eq5557 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5414 eq182
    | exact resolve eq182 eq5414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq5558 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5414 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq5414
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq5414
       grind)
    | exact resolve eq12 eq5414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5566 : ∀ X0 X1 : G, (M.op X0 (M.op X1 (σ x))) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1
    first
    | exact superpose eq5414 eq183
    | exact resolve eq183 eq5414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183
  have eq5568 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (σ y))) = (M.op X0 (M.op X2 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq5414 eq568
    | exact resolve eq568 eq5414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq5414
  have eq5578 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5558
  have eq5585 : ∀ X0 X2 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (M.op X2 (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0 X2
    first
    | exact superpose eq571 eq5568
    | (have j0 := eq5568 X0 (σ x) X2
       grind)
    | exact resolve eq5568 eq571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5568
  have eq5592 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5578
    | exact resolve eq5578 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5578
  have eq5593 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq5592
  have eq5594 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5557 eq5555
    | exact resolve eq5555 eq5557
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5555 eq5557
  have eq5597 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq5566 eq5585
    | exact resolve eq5585 eq5566
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5566 eq5585
  have eq5600 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5341 eq5593
    | exact resolve eq5593 eq5341
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5341 eq5593
  have eq5601 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5552 eq5594
    | exact resolve eq5594 eq5552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5552 eq5594
  have eq5605 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5600
    | exact resolve eq5600 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5600
  have eq5606 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5597 eq5601
    | exact resolve eq5601 eq5597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5597 eq5601
  have eq5608 : (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq5606
    | exact resolve eq5606 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5606
  have eq5609 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5605 eq5608
    | exact resolve eq5608 eq5605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5608
  have eq5637 : (σ x) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5605
  have eq5706 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5514 eq1427
    | exact resolve eq1427 eq5514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1427 eq5514
  have eq5788 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5609 eq13
    | (have j0 := eq13 (σ y) (σ y)
       grind)
    | (have r₁ := eq13 (σ y) (σ y)
       have r₂ := eq5609
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq5609
       grind)
    | exact resolve eq13 eq5609
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5609
  have eq5803 : (σ y) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5788
  have eq5848 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5706 eq1195
    | exact resolve eq1195 eq5706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1195 eq5706
  have eq5876 : (σ y) = (k (σ y) (σ (M.op x y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq5848
    | exact resolve eq5848 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5848
  have eq5879 : (σ y) = (k (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5524 eq5876
    | exact resolve eq5876 eq5524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5524 eq5876
  have eq5892 : (τ (σ y)) = (k (τ (σ y)) y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq5803 eq152
    | exact resolve eq152 eq5803
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq152 eq5803
  have eq5898 : y = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31 eq5892
    | exact resolve eq5892 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq5892
  have eq5917 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5879 eq874
    | (have j0 := eq874 (σ y) (σ y)
       grind)
    | (have r₁ := eq874 (σ y) (σ y)
       have r₂ := eq5879
       grind)
    | exact resolve eq874 eq5879
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5879
  have eq5918 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq5917
  have eq5919 : (σ y) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq5918
  have eq5941 : y ≠ y ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq874 y y
       have i₂ := eq5898
       grind)
    | exact superpose eq5898 eq874
    | (have j0 := eq874 y y
       grind)
    | (have r₁ := eq874 y y
       have r₂ := eq5898
       grind)
    | exact resolve eq874 eq5898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq874 eq5898
  have eq5942 : y ≠ y ∨ y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5941
  have eq5943 : y = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq5942
  have eq5953 : ∀ X0 : G, (M.op X0 (M.op (σ x) (σ y))) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5919 eq571
    | exact resolve eq571 eq5919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq571
  have eq5977 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq4208 eq5953
    | exact resolve eq5953 eq4208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5953
  have eq6042 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq569 X0 y
       have i₂ := eq5943
       grind)
    | exact superpose eq5943 eq569
    | exact resolve eq569 eq5943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq7216 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5977 eq26
    | (have j1 := eq5977 (σ x)
       grind)
    | exact resolve eq26 eq5977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq7218 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq5977 eq5919
    | exact resolve eq5919 eq5977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5919 eq5977
  have eq7222 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq7218
  have eq7226 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq4208 eq7216
    | exact resolve eq7216 eq4208
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4208 eq7216
  have eq7315 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7222 eq4224
    | exact resolve eq4224 eq7222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4224 eq7222
  have eq7343 : (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq7315
  have eq7367 : (σ x) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7226 eq7343
    | exact resolve eq7343 eq7226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7226 eq7343
  have eq7382 : x = (M.op x y) := by
    first
    | (have r₁ := eq7367
       have r₂ := eq5537
       grind)
    | exact resolve eq7367 eq5537
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5537 eq7367
  have eq7389 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq7382
       grind)
    | exact superpose eq7382 eq18
    | exact resolve eq18 eq7382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq7390 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq7382
       grind)
    | exact superpose eq7382 eq22
    | exact resolve eq22 eq7382
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq7382
  have eq7414 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq7390 eq20
    | exact resolve eq20 eq7390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq8173 : y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5943
       have i₂ := eq6042 y
       grind)
    | exact superpose eq6042 eq5943
    | exact resolve eq5943 eq6042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5943
  have eq8175 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7389
       have i₂ := eq6042 sF0
       grind)
    | exact superpose eq6042 eq7389
    | exact resolve eq7389 eq6042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6042 eq7389
  have eq8180 : y = (M.op y (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8173
  have eq8186 : y = (M.op (M.op x y) (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq764 eq8180
    | exact resolve eq8180 eq764
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq764 eq8180
  have eq8222 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8175 eq8186
    | exact resolve eq8186 eq8175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8175 eq8186
  have eq8240 : (σ (M.op x y)) ≠ (σ x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq8222 eq27
    | exact resolve eq27 eq8222
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8222
  have eq8273 : y = (M.op x y) := by
    first
    | (have r₁ := eq8240
       have r₂ := eq7414
       grind)
    | exact resolve eq8240 eq7414
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8240
  have eq8275 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq8273
       grind)
    | exact superpose eq8273 eq24
    | exact resolve eq24 eq8273
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq8273
  have eq8313 : (σ x) = (σ y) := by
    first
    | exact superpose eq7390 eq8275
    | exact resolve eq8275 eq7390
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7390 eq8275
  have eq8355 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq8313 eq5637
    | (have r₁ := eq5637
       have r₂ := eq8313
       grind)
    | exact resolve eq5637 eq8313
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5637 eq8313
  have eq8363 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq8355
  have eq8420 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq8363 eq27
    | exact resolve eq27 eq8363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq8363
  have eq8464 : False := by grind
  exact eq8464

/-- `Equation455`: `x = x ◇ (y ◇ (z ◇ (z ◇ y)))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if m(X,Y) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_pxy_x_pxy_x_pyx_Equation455 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law455 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law455.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ M.op a b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 (M.op X2 X1)))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq27 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 (k X0 (τ X1)) X2
       have i₂ := eq18 X1 X0
       grind)
    | exact superpose eq18 eq15
    | exact resolve eq15 eq18
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
  clear eq22
  have eq63 : ∀ X0 X1 : G, (M.op X1 (M.op X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 (M.op X0 X0) X0
       have i₂ := eq9 (M.op X0 X0) X0 X0
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k (M.op X1 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X1 X1) X0
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq12
    | (have j0 := eq12 (M.op X1 X1) X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X1
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq93 : ∀ X0 X1 : G, (k (M.op X1 X1) X0) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq90 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq136 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X0) ∨ (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 (M.op X1 X1)
       have i₂ := eq63 X1 X0
       grind)
    | exact superpose eq63 eq13
    | (have j0 := eq13 X0 (M.op X1 X1)
       grind)
    | (have r₁ := eq13 X1 (M.op X0 X0)
       have r₂ := eq63 X0 X1
       grind)
    | exact resolve eq13 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 ∨ (M.op X1 X1) = (M.op (M.op X1 X1) X0) := by
    intro X0 X1
    first
    | (have j0 := eq136 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq400 : ∀ X0 : G, X0 ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq14 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq401 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq400 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq400
  have eq405 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq401 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq401 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq401 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq425 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq405 (σ X0)
       grind)
    | exact superpose eq405 eq15
    | exact resolve eq15 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq428 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k (k X0 (τ (σ X0))) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq27 X0 (σ X0) X1
       have i₂ := eq405 (σ X0)
       grind)
    | exact superpose eq405 eq27
    | exact resolve eq27 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq431 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq405 (τ X0)
       grind)
    | exact superpose eq405 eq31
    | exact resolve eq31 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq440 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq431 X0
       have i₂ := eq405 X0
       grind)
    | exact superpose eq405 eq431
    | exact resolve eq431 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq443 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k (k X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq428 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq428
    | exact resolve eq428 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq446 : ∀ X0 : G, (σ (M.op X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq425 X0
       have i₂ := eq405 X0
       grind)
    | exact superpose eq405 eq425
    | exact resolve eq425 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425
  have eq462 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) (σ X1)) = (σ (k (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq443 X0 X1
       have i₂ := eq405 X0
       grind)
    | exact superpose eq405 eq443
    | exact resolve eq443 eq405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq443
  have eq476 : ∀ X0 X1 : G, (k (M.op (σ X0) (σ X0)) (σ X1)) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq462 X0 X1
       have i₂ := eq93 X1 X0
       grind)
    | exact superpose eq93 eq462
    | exact resolve eq462 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq462
  have eq485 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (σ X1)) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq476 X0 X1
       have i₂ := eq93 (σ X1) (σ X0)
       grind)
    | exact superpose eq93 eq476
    | exact resolve eq476 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq489 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X1)) = (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq485 X0 X1
       have i₂ := eq446 X0
       grind)
    | exact superpose eq446 eq485
    | exact resolve eq485 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq485
  have eq503 : ∀ X0 X1 : G, (k X1 (σ (M.op X0 X0))) = X1 ∨ (σ (M.op X0 X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq139 X0 (σ X0)
       have i₂ := eq446 X0
       grind)
    | exact superpose eq446 eq139
    | exact resolve eq139 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq507 : ∀ X0 X1 : G, (M.op X1 (σ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63 (σ X0) X1
       have i₂ := eq446 X0
       grind)
    | exact superpose eq446 eq63
    | exact resolve eq63 eq446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq446
  have eq582 : ∀ X0 X1 : G, (M.op X1 (τ (M.op X0 X0))) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq63 (τ X0) X1
       have i₂ := eq440 X0
       grind)
    | exact superpose eq440 eq63
    | exact resolve eq63 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq583 : ∀ X0 X1 : G, (k (τ (M.op X0 X0)) X1) = (M.op (τ (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq93 X0 (τ X0)
       have i₂ := eq440 X0
       grind)
    | exact superpose eq440 eq93
    | exact resolve eq93 eq440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq440
  have eq604 : ∀ X0 X1 X2 : G, (M.op X2 (τ (M.op X0 (M.op X1 (M.op X1 X0))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq582 (M.op X0 (M.op X1 (M.op X1 X0))) X2
       have i₂ := eq9 (M.op X0 (M.op X1 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq9 eq582
    | exact resolve eq582 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq582
  have eq1116 : ∀ X0 X1 X2 : G, (M.op X1 (τ (M.op X2 (M.op X0 X0)))) = X1 ∨ (M.op X2 X0) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq604 X2 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq604
    | (have j1 := eq14 X2 X0
       grind)
    | exact resolve eq604 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1193 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X0 X2) ∨ (M.op X2 X0) = X2 ∨ (M.op X1 (τ X2)) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1116 X0 X1 X2
       have i₂ := eq63 X0 X2
       grind)
    | exact superpose eq63 eq1116
    | (have j0 := eq1116 X0 X1 X2
       grind)
    | exact resolve eq1116 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1116
  have eq2004 : ∀ X0 X1 : G, (k (M.op X0 X0) (σ X1)) = (σ (M.op (τ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (M.op X0 X0) X1
       have i₂ := eq583 X0 X1
       grind)
    | exact superpose eq583 eq17
    | exact resolve eq17 eq583
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq583
  have eq2024 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (σ X1)) = (σ (M.op (τ (M.op X0 X0)) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2004 X0 X1
       have i₂ := eq93 (σ X1) X0
       grind)
    | exact superpose eq93 eq2004
    | exact resolve eq2004 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2004
  have eq2730 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) X1)) ∨ (k (σ X1) (σ (M.op X0 X0))) = (M.op (σ X1) (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ (M.op X0 X0))
       have i₂ := eq489 X0 X1
       grind)
    | exact superpose eq489 eq12
    | (have j0 := eq12 (σ X1) (σ (M.op X0 X0))
       grind)
    | exact resolve eq12 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2751 : ∀ X0 X1 : G, (σ X1) = (k (σ X1) (σ (M.op X0 X0))) ∨ (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2730 X0 X1
       have i₂ := eq507 X0 (σ X1)
       grind)
    | exact superpose eq507 eq2730
    | (have j0 := eq2730 X0 X1
       grind)
    | exact resolve eq2730 eq507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2730
  have eq2775 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) X1)) ∨ (σ X1) = (σ (k X1 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq2751 X0 X1
       have i₂ := eq15 X1 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq2751
    | (have j0 := eq2751 X0 X1
       grind)
    | exact resolve eq2751 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2751
  have eq22493 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) ∨ (M.op X2 (τ (σ X1))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq1193 (σ X0) X2 (σ X1)
       grind)
    | exact superpose eq1193 eq15
    | (have j1 := eq1193 (σ X0) X2 (σ X1)
       grind)
    | exact resolve eq15 eq1193
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1193
  have eq22529 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op X2 X1) = X2 ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq22493 X0 X1 X2
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq22493
    | (have j0 := eq22493 X0 X1 X2
       grind)
    | exact resolve eq22493 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22493
  have eq33420 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X1 X1))) ∨ (σ (M.op X1 X1)) = (M.op (σ (M.op X1 X1)) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 (M.op X1 X1)
       have i₂ := eq503 X1 (σ X0)
       grind)
    | exact superpose eq503 eq15
    | (have j1 := eq503 X1 (σ X0)
       grind)
    | exact resolve eq15 eq503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq33449 : ∀ X0 X1 : G, (σ (M.op X1 X1)) = (σ (M.op (M.op X1 X1) X0)) ∨ (σ X0) = (σ (k X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq33420 X0 X1
       have i₂ := eq489 X1 X0
       grind)
    | exact superpose eq489 eq33420
    | (have j0 := eq33420 X0 X1
       grind)
    | exact resolve eq33420 eq489
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489 eq33420
  have eq33498 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq33449 X0 X1
       have j1 := eq2775 X1 X0
       grind)
    | (have r₁ := eq33449 X1 X0
       have r₂ := eq2775 X0 X1
       grind)
    | exact resolve eq33449 eq2775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2775 eq33449
  have eq33658 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (M.op X1 X1))
       have i₂ := eq33498 X0 X1
       grind)
    | exact superpose eq33498 eq10
    | exact resolve eq10 eq33498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33660 : ∀ X0 X1 X2 : G, (k (σ X1) (σ X0)) = (σ (k X1 (k X0 (M.op X2 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X1 (k X0 (M.op X2 X2))
       have i₂ := eq33498 X0 X2
       grind)
    | exact superpose eq33498 eq15
    | exact resolve eq15 eq33498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33719 : ∀ X0 X1 X2 : G, (σ (k X1 X0)) = (σ (k X1 (k X0 (M.op X2 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33660 X0 X1 X2
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq33660
    | exact resolve eq33660 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33660
  have eq33721 : ∀ X0 X1 : G, (k X0 (M.op X1 X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq33658 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq33658
    | exact resolve eq33658 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33658
  have eq33778 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 (M.op X1 (M.op X1 X0)))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33721 X2 (M.op X0 (M.op X1 (M.op X1 X0)))
       have i₂ := eq9 (M.op X0 (M.op X1 (M.op X1 X0))) X0 X1
       grind)
    | exact superpose eq9 eq33721
    | exact resolve eq33721 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33817 : ∀ X0 X1 X2 : G, (k X2 (τ (M.op X0 (M.op X1 (M.op X1 X0))))) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33721 X2 (τ (M.op X0 (M.op X1 (M.op X1 X0))))
       have i₂ := eq604 X0 X1 (τ (M.op X0 (M.op X1 (M.op X1 X0))))
       grind)
    | exact superpose eq604 eq33721
    | exact resolve eq33721 eq604
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq604
  have eq35867 : ∀ X0 X1 X2 : G, (k X1 (M.op X2 (M.op X0 X0))) = X1 ∨ (M.op X2 X0) = X2 ∨ (k X2 X0) = (M.op X0 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33778 X2 X0 X1
       have i₂ := eq14 X2 X0
       grind)
    | exact superpose eq14 eq33778
    | (have j1 := eq14 X2 X0
       grind)
    | exact resolve eq33778 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36085 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X0 X2) ∨ (M.op X2 X0) = X2 ∨ (k X1 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35867 X0 X1 X2
       have i₂ := eq63 X0 X2
       grind)
    | exact superpose eq63 eq35867
    | (have j0 := eq35867 X0 X1 X2
       grind)
    | exact resolve eq35867 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35867
  have eq61312 : ∀ X0 X1 X2 X3 : G, (σ (k X2 X0)) = (σ (M.op (k X0 (M.op X1 X1)) X2)) ∨ (M.op X2 (k X0 (M.op X1 X1))) = X2 ∨ (k X3 X2) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq33719 X0 X2 X1
       have i₂ := eq36085 (k X0 (M.op X1 X1)) X3 X2
       grind)
    | exact superpose eq36085 eq33719
    | (have j1 := eq36085 (k X0 (M.op X1 X1)) X3 X2
       grind)
    | exact resolve eq33719 eq36085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33719 eq36085
  have eq61362 : ∀ X0 X1 X2 X3 : G, (σ (M.op X0 X2)) = (σ (k X2 X0)) ∨ (M.op X2 (k X0 (M.op X1 X1))) = X2 ∨ (k X3 X2) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq61312 X0 X1 X2 X3
       have i₂ := eq33721 X0 X1
       grind)
    | exact superpose eq33721 eq61312
    | (have j0 := eq61312 X0 X1 X2 X3
       grind)
    | exact resolve eq61312 eq33721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61312
  have eq61368 : ∀ X0 X2 X3 : G, (σ (M.op X0 X2)) = (σ (k X2 X0)) ∨ (M.op X2 X0) = X2 ∨ (k X3 X2) = X3 := by
    intro X0 X2 X3
    first
    | (have i₁ := eq61362 X0 x X2 X3
       have i₂ := eq33721 X0 x
       grind)
    | exact superpose eq33721 eq61362
    | (have j0 := eq61362 X0 x X2 X3
       grind)
    | exact resolve eq61362 eq33721
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61362
  have eq1359663 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op X0 y) = X0 ∨ (σ y) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq22529 x y X0
       grind)
    | exact superpose eq22529 eq16
    | (have j1 := eq22529 x y X0
       grind)
    | exact resolve eq16 eq22529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22529
  have eq1362214 : ∀ X0 X1 : G, (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op X0 y) = X0 ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op y x) ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1359663 X0
       have i₂ := eq61368 x y X1
       grind)
    | exact superpose eq61368 eq1359663
    | (have j0 := eq1359663 X0
       have j1 := eq61368 x y X1
       grind)
    | (have r₁ := eq1359663 X0
       have r₂ := eq61368 x y x
       grind)
    | exact resolve eq1359663 eq61368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61368 eq1359663
  have eq1362228 : ∀ X0 X1 : G, y = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op X0 y) = X0 ∨ (k X1 y) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq1362214 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362214
  have eq1979390 : ∀ X0 X1 X2 : G, (k X0 (M.op x (M.op y y))) = X0 ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (M.op X1 y) = X1 ∨ (k X2 y) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq33778 x y X0
       have i₂ := eq1362228 X1 X2
       grind)
    | exact superpose eq1362228 eq33778
    | (have j1 := eq1362228 X1 X2
       grind)
    | exact resolve eq33778 eq1362228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33778 eq1362228
  have eq1979476 : ∀ X0 X1 X2 : G, (σ y) = (M.op (σ y) (σ x)) ∨ (k X0 x) = X0 ∨ (M.op X1 y) = X1 ∨ (k X2 y) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1979390 X0 X1 X2
       have i₂ := eq63 y x
       grind)
    | exact superpose eq63 eq1979390
    | (have j0 := eq1979390 X0 X1 X2
       grind)
    | exact resolve eq1979390 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1979390
  have eq2069479 : ∀ X0 X1 X2 X3 : G, (k X0 (τ (M.op (σ x) (M.op (σ y) (σ y))))) = X0 ∨ (k X1 x) = X1 ∨ (M.op X2 y) = X2 ∨ (k X3 y) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq33817 (σ x) (σ y) X0
       have i₂ := eq1979476 X1 X2 X3
       grind)
    | exact superpose eq1979476 eq33817
    | (have j1 := eq1979476 X1 X2 X3
       grind)
    | exact resolve eq33817 eq1979476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33817 eq1979476
  have eq2069561 : ∀ X0 X1 X2 X3 : G, (k X0 (τ (σ x))) = X0 ∨ (k X1 x) = X1 ∨ (M.op X2 y) = X2 ∨ (k X3 y) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2069479 X0 X1 X2 X3
       have i₂ := eq63 (σ y) (σ x)
       grind)
    | exact superpose eq63 eq2069479
    | (have j0 := eq2069479 X0 X1 X2 X3
       grind)
    | exact resolve eq2069479 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2069479
  have eq2069740 : ∀ X0 X1 X2 X3 : G, (k X3 y) = X3 ∨ (k X1 x) = X1 ∨ (M.op X2 y) = X2 ∨ (k X0 x) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq2069561 X1 X0 X2 X3
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2069561
    | (have j0 := eq2069561 X0 X1 X2 X3
       grind)
    | exact resolve eq2069561 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2069561
  have eq2070013 : ∀ X0 X1 X2 : G, (k X0 x) = X0 ∨ y = (M.op y y) ∨ (M.op X1 y) = X1 ∨ (k X2 x) = X2 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq405 y
       have i₂ := eq2069740 X2 X0 X1 y
       grind)
    | exact superpose eq2069740 eq405
    | (have j1 := eq2069740 X0 X0 y x
       grind)
    | exact resolve eq405 eq2069740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2069740
  have eq2071216 : ∀ X0 X1 : G, X0 ≠ X0 ∨ y = (M.op y y) ∨ (M.op X1 y) = X1 ∨ (k X0 x) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq2070013 X0 y X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2070013
  have eq2071217 : ∀ X0 X1 : G, (k X0 x) = X0 ∨ (M.op X1 y) = X1 ∨ y = (M.op y y) := by
    intro X0 X1
    first
    | (have j0 := eq2071216 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2071216
  have eq2071323 : ∀ X0 : G, y = (M.op y y) ∨ (M.op X0 y) = X0 ∨ x = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq405 x
       have i₂ := eq2071217 x X0
       grind)
    | exact superpose eq2071217 eq405
    | (have j1 := eq2071217 X0 y
       grind)
    | exact resolve eq405 eq2071217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq405 eq2071217
  have eq2072626 : y ≠ y ∨ y = (M.op y y) ∨ x = (M.op x x) := by
    first
    | (have j0 := eq2071323 y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2071323
  have eq2072627 : x = (M.op x x) ∨ y = (M.op y y) := by grind
  clear eq2072626
  have eq2072726 : ∀ X0 : G, y = (M.op y y) ∨ (M.op x X0) = (k x X0) := by
    intro X0
    first
    | (have i₁ := eq93 X0 x
       have i₂ := eq2072627
       grind)
    | exact superpose eq2072627 eq93
    | exact resolve eq93 eq2072627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq2072747 : ∀ X0 : G, y = (M.op y y) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq507 x X0
       have i₂ := eq2072627
       grind)
    | exact superpose eq2072627 eq507
    | exact resolve eq507 eq2072627
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2072627
  have eq2078028 : ∀ X0 X1 : G, (M.op X0 (σ y)) = X0 ∨ (M.op X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq507 y X0
       have i₂ := eq2072747 X1
       grind)
    | exact superpose eq2072747 eq507
    | (have j1 := eq2072747 X1
       grind)
    | exact resolve eq507 eq2072747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq507
  have eq2078338 : ∀ X0 X1 : G, (σ X0) = (σ (k X0 y)) ∨ (M.op X1 (σ x)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq33498 X0 y
       have i₂ := eq2072747 X1
       grind)
    | exact superpose eq2072747 eq33498
    | (have j1 := eq2072747 X1
       grind)
    | exact resolve eq33498 eq2072747
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33498 eq2072747
  have eq2093508 : ∀ X0 X1 : G, (M.op x X1) = (k x X1) ∨ (M.op X0 y) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq63 y X0
       have i₂ := eq2072726 X1
       grind)
    | exact superpose eq2072726 eq63
    | (have j1 := eq2072726 X1
       grind)
    | exact resolve eq63 eq2072726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63
  have eq2093895 : ∀ X0 X1 : G, (k X0 y) = X0 ∨ (M.op x X1) = (k x X1) := by
    intro X0 X1
    first
    | (have i₁ := eq33721 X0 y
       have i₂ := eq2072726 X1
       grind)
    | exact superpose eq2072726 eq33721
    | (have j1 := eq2072726 X1
       grind)
    | exact resolve eq33721 eq2072726
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33721 eq2072726
  have eq2110340 : ∀ X0 : G, (σ (M.op x y)) ≠ (σ x) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq16
       have i₂ := eq2078028 (σ x) X0
       grind)
    | exact superpose eq2078028 eq16
    | (have j1 := eq2078028 X0 X0
       grind)
    | exact resolve eq16 eq2078028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078028
  have eq2126068 : x ≠ (M.op x y) ∨ (M.op x y) = (k x y) := by
    first
    | (have j0 := eq2093895 x y
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2093895
  have eq2126074 : (M.op x y) = (k x y) := by
    first
    | (have j1 := eq2093508 x y
       grind)
    | (have r₁ := eq2126068
       have r₂ := eq2093508 x x
       grind)
    | exact resolve eq2126068 eq2093508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2093508 eq2126068
  have eq2164201 : ∀ X0 : G, (σ (M.op x y)) = (σ x) ∨ (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq2078338 x X0
       have i₂ := eq2126074
       grind)
    | exact superpose eq2126074 eq2078338
    | (have j0 := eq2078338 X0 X0
       grind)
    | exact resolve eq2078338 eq2126074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2078338 eq2126074
  have eq2164845 : ∀ X0 : G, (M.op X0 (σ x)) = X0 := by
    intro X0
    first
    | (have j0 := eq2164201 X0
       have j1 := eq2110340 X0
       grind)
    | (have r₁ := eq2164201 X0
       have r₂ := eq2110340 X0
       grind)
    | exact resolve eq2164201 eq2110340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2110340 eq2164201
  have eq2165012 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op (τ (σ x)) X0)) := by
    intro X0
    first
    | (have i₁ := eq2024 (σ x) x
       have i₂ := eq2164845 (σ x)
       grind)
    | exact superpose eq2164845 eq2024
    | exact resolve eq2024 eq2164845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2024 eq2164845
  have eq2167478 : ∀ X0 : G, (M.op (σ x) (σ X0)) = (σ (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq2165012 X0
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq2165012
    | exact resolve eq2165012 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2165012
  have eq2237240 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2167478 y
       grind)
    | exact superpose eq2167478 eq16
    | (have r₁ := eq16
       have r₂ := eq2167478 y
       grind)
    | exact resolve eq16 eq2167478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2167478
  have eq2238420 : False := by grind
  exact eq2238420
