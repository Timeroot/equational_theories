import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = Y then m(X,Y) else if X = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_y_x_y_pxy_pxx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = b ∨ a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq27 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 (M.op X1 x)
       have i₂ := eq9 X0 X1 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X1 : G, (M.op X1 X1) = (k X1 X1) := by
    intro X1
    grind
  have eq64 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq19 X0 (τ X0)
       have i₂ := eq47 (τ X0)
       grind)
    | exact superpose eq47 eq19
    | exact resolve eq19 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq67 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq64
    | exact resolve eq64 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq73 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq67 X0
       have i₂ := eq47 X0
       grind)
    | exact superpose eq47 eq67
    | exact resolve eq67 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47 eq67
  have eq85 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X0) X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X0)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq85 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq85
    | (have j0 := eq85 (σ (k X0 X1)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq85 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq117 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq73 X1
       have i₂ := eq27 X0 (τ X1)
       grind)
    | exact superpose eq27 eq73
    | exact resolve eq73 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq357 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq117 x X1
       have i₂ := eq27 x X0
       grind)
    | exact superpose eq27 eq117
    | exact resolve eq117 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq117
  have eq401 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq86 x y
       grind)
    | exact superpose eq86 eq16
    | (have j1 := eq86 x y
       grind)
    | exact resolve eq16 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq758 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq401
       have i₂ := eq85 x y
       grind)
    | exact superpose eq85 eq401
    | (have j1 := eq85 (σ x) (σ y)
       grind)
    | (have r₁ := eq401
       have r₂ := eq85 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq401
       have r₂ := eq85 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq401 eq85
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85 eq401
  have eq759 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq758
  have eq760 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq759
       grind)
    | exact superpose eq759 eq16
    | exact resolve eq16 eq759
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq759
  have eq761 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq760
       have r₂ := eq357 x (σ x)
       grind)
    | exact resolve eq760 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq760
  have eq763 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq761
       grind)
    | exact superpose eq761 eq10
    | exact resolve eq10 eq761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq761
  have eq775 : x = y := by
    first
    | (have i₁ := eq763
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq763
    | exact resolve eq763 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq763
  have eq777 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq775
       grind)
    | exact superpose eq775 eq16
    | exact resolve eq16 eq775
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq775
  have eq778 : False := by grind
  exact eq778

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_pyy_pxy_pyy_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq93 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
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
    | (have r₁ := eq13 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq93 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq98 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq97 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq664 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq98 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq682 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq664 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq664 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq664 X1 X1
       have r₂ := eq14 X1 X1
       grind)
    | (have r₁ := eq664 X0 X1
       have r₂ := eq14 (M.op X0 X1) X1
       grind)
    | exact resolve eq664 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq698 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq682 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq682
  have eq798 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq698 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq698
  have eq917 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq798 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq798
  have eq918 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq917 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq917
  have eq942 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  clear eq918
  have eq977 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq942 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq942
  have eq985 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq977 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq977
    | exact resolve eq977 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq995 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq985 X0 X1
       have i₂ := eq977 X0 X1
       grind)
    | exact superpose eq977 eq985
    | exact resolve eq985 eq977
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq977 eq985
  have eq999 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq995 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq995
  have eq1019 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq999 x y
       grind)
    | exact superpose eq999 eq16
    | (have r₁ := eq16
       have r₂ := eq999 x y
       grind)
    | exact resolve eq16 eq999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq999
  have eq1048 : False := by grind
  exact eq1048

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = X then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_x_pxy_x_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
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
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X1 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 (M.op X0 X2))) X1) = (M.op (M.op X0 (M.op X1 (M.op X0 X2))) X1) := by
    intro X0 X1 X2
    grind
  have eq77 : x ≠ (M.op x y) ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | (have i₁ := eq12 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq12
    | (have j0 := eq12 x y
       grind)
    | exact resolve eq12 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : (σ x) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq12
    | (have j0 := eq12 (σ x) (σ y)
       grind)
    | exact resolve eq12 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq115
    | exact resolve eq115 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq117
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq117
    | exact resolve eq117 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq242 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 x X0
       have i₂ := eq56 x X1
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1123 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) X1) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq67 x X1 (M.op X0 (M.op X1 (M.op X0 x)))
       have i₂ := eq54 X0 X1 x x
       grind)
    | exact superpose eq54 eq67
    | exact resolve eq67 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq67
  have eq1151 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1123 X0 X1
       have i₂ := eq250 X0 X0
       grind)
    | exact superpose eq250 eq1123
    | exact resolve eq1123 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq1123
  have eq1356 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq96 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq16123 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq118 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16124 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq16123
    | exact resolve eq16123 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16123
  have eq16135 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq16124
       have r₂ := eq28
       grind)
    | exact resolve eq16124 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16124
  have eq16137 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq16135
    | exact resolve eq16135 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16135
  have eq16141 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq16137
  have eq16184 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq16141
    | exact resolve eq16141 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16141
  have eq16865 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq16184 eq118
    | exact resolve eq118 eq16184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16184
  have eq16873 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16865
  have eq16875 : x = (M.op y y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq16873
       have r₂ := eq28
       grind)
    | exact resolve eq16873 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16873
  have eq16880 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq16875
  have eq16922 : (M.op x y) = (k x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16880
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16880
    | exact resolve eq16880 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16880
  have eq17621 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq16922
       grind)
    | exact superpose eq16922 eq45
    | exact resolve eq45 eq16922
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16922
  have eq17635 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq17621
    | exact resolve eq17621 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17621
  have eq17843 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq17635 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq17635
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17846 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq17843
    | exact resolve eq17843 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17843
  have eq17857 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq17846
       have r₂ := eq28
       grind)
    | exact resolve eq17846 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17846
  have eq17859 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq17857
    | exact resolve eq17857 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17857
  have eq17860 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17859
  have eq17866 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq17860
  have eq17912 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq17866
    | exact resolve eq17866 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17866
  have eq18431 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq17912 eq17635
    | exact resolve eq17635 eq17912
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17635 eq17912
  have eq18433 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq18431
  have eq18437 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq18433
       have r₂ := eq28
       grind)
    | exact resolve eq18433 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18433
  have eq18439 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18437 eq28
    | exact resolve eq28 eq18437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18441 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18437 eq78
    | (have r₁ := eq78
       have r₂ := eq18437
       grind)
    | exact resolve eq78 eq18437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq18437
  have eq18445 : (σ x) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq18441
  have eq20098 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq18445 eq118
    | exact resolve eq118 eq18445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20113 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq20098
  have eq20127 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq20113
       have r₂ := eq18439
       grind)
    | exact resolve eq20113 eq18439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20113
  have eq20136 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by grind
  clear eq20127
  have eq20186 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq20136
    | exact resolve eq20136 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20136
  have eq21294 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20186 eq118
    | exact resolve eq118 eq20186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq20186
  have eq21306 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by grind
  clear eq21294
  have eq21310 : x = (M.op y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq21306
       have r₂ := eq28
       grind)
    | exact resolve eq21306 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21306
  have eq21316 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by grind
  clear eq21310
  have eq21365 : (M.op x y) = (k x y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21316
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq21316
    | exact resolve eq21316 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21316
  have eq21651 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq21365
       grind)
    | exact superpose eq21365 eq45
    | exact resolve eq45 eq21365
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21365
  have eq21665 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21 eq21651
    | exact resolve eq21651 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21651
  have eq21743 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21665 eq18445
    | exact resolve eq18445 eq21665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18445
  have eq21747 : (σ (M.op x y)) = (σ x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21743
  have eq21755 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq21747
       have r₂ := eq18439
       grind)
    | exact resolve eq21747 eq18439
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18439 eq21747
  have eq21775 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21755
  have eq21828 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq27 eq21775
    | exact resolve eq21775 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21775
  have eq23059 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21828 eq21665
    | exact resolve eq21665 eq21828
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21665 eq21828
  have eq23062 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq23059
  have eq23071 : x = (M.op x y) := by
    first
    | (have r₁ := eq23062
       have r₂ := eq28
       grind)
    | exact resolve eq23062 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23062
  have eq23073 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq23071 eq21
    | exact resolve eq21 eq23071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21
  have eq23079 : x ≠ x ∨ x = (M.op y y) ∨ x = (k x y) := by
    first
    | exact superpose eq23071 eq77
    | (have r₁ := eq77
       have r₂ := eq23071
       grind)
    | exact resolve eq77 eq23071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq23146 : x = (k x y) ∨ x = (M.op y y) := by grind
  clear eq23079
  have eq23196 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq23073
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq23073
    | exact resolve eq23073 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23073
  have eq23202 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq23196 eq27
    | exact resolve eq27 eq23196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27291 : (σ x) = (k (σ x) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq23146
       grind)
    | exact superpose eq23146 eq45
    | exact resolve eq45 eq23146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27301 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq1356 x y
       have i₂ := eq23146
       grind)
    | exact superpose eq23146 eq1356
    | (have j0 := eq1356 x y
       grind)
    | exact resolve eq1356 eq23146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23146
  have eq27304 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq27301
  have eq27311 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27304
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq27304
    | exact resolve eq27304 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27304
  have eq27319 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23196 eq27291
    | exact resolve eq27291 eq23196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27291
  have eq27321 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27311
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27311
    | exact resolve eq27311 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27311
  have eq27329 : (σ x) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27319
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27319
    | exact resolve eq27319 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27319
  have eq27330 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq27321
    | exact resolve eq27321 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27321
  have eq27336 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23196 eq27329
    | exact resolve eq27329 eq23196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27329
  have eq27337 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23196 eq27330
    | exact resolve eq27330 eq23196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27330
  have eq27339 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq27337
       have r₂ := eq28
       grind)
    | exact resolve eq27337 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27337
  have eq27341 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27339
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq27339
    | exact resolve eq27339 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27339
  have eq27343 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq27341
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq27341
    | exact resolve eq27341 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27341
  have eq27345 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23196 eq27343
    | exact resolve eq27343 eq23196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27343
  have eq28901 : (k (σ (M.op x y)) (σ y)) = (M.op (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq27345
  have eq28967 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq23202 eq28901
    | exact resolve eq28901 eq23202
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28901
  have eq31004 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq28967 eq27336
    | exact resolve eq27336 eq28967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27336 eq28967
  have eq31010 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq31004
  have eq31012 : x = (M.op y y) := by
    first
    | (have r₁ := eq31010
       have r₂ := eq28
       grind)
    | exact resolve eq31010 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31010
  have eq31024 : ∀ X0 : G, (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq31012
       have i₂ := eq242 y X0
       grind)
    | (have i₁ := eq31012
       have i₂ := eq242 X0 y
       grind)
    | exact superpose eq242 eq31012
    | exact resolve eq31012 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq31029 : (M.op x y) = (k x y) := by grind
  have eq31049 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1151 y x
       have i₂ := eq31012
       grind)
    | exact superpose eq31012 eq1151
    | exact resolve eq1151 eq31012
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1151 eq31012
  have eq31089 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq31029
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq31029
    | exact resolve eq31029 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq31029
  have eq31097 : x = (k x y) := by
    first
    | exact superpose eq23071 eq31089
    | exact resolve eq31089 eq23071
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23071 eq31089
  have eq31586 : (σ x) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq31097
       grind)
    | exact superpose eq31097 eq45
    | exact resolve eq45 eq31097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq31598 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1356 x y
       have i₂ := eq31097
       grind)
    | exact superpose eq31097 eq1356
    | (have j0 := eq1356 x y
       grind)
    | exact resolve eq1356 eq31097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356 eq31097
  have eq31601 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq31598
  have eq31607 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq31601
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq31601
    | exact resolve eq31601 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq31601
  have eq31617 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq23196 eq31586
    | exact resolve eq31586 eq23196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31586
  have eq31618 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq31607
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31607
    | exact resolve eq31607 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31607
  have eq31628 : (σ x) = (k (σ (M.op x y)) (σ y)) := by
    first
    | (have i₁ := eq31617
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31617
    | exact resolve eq31617 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31617
  have eq31629 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq31618
    | exact resolve eq31618 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq31618
  have eq31637 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq23196 eq31628
    | exact resolve eq31628 eq23196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31628
  have eq31638 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq23196 eq31629
    | exact resolve eq31629 eq23196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31629
  have eq31642 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq31638
       have r₂ := eq28
       grind)
    | exact resolve eq31638 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31638
  have eq31646 : x = (σ x) := by
    first
    | (have i₁ := eq31642
       have i₂ := eq31024 (σ y)
       grind)
    | exact superpose eq31024 eq31642
    | exact resolve eq31642 eq31024
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31024 eq31642
  have eq31650 : x = (σ x) := by
    first
    | (have i₁ := eq31646
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq31646
    | exact resolve eq31646 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq31646
  have eq31654 : x = (σ (M.op x y)) := by
    first
    | exact superpose eq23196 eq31650
    | exact resolve eq31650 eq23196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23196 eq31650
  have eq31724 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq31654 eq23202
    | exact resolve eq23202 eq31654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23202
  have eq36860 : x = (k x (σ y)) := by
    first
    | exact superpose eq31654 eq31637
    | exact resolve eq31637 eq31654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31637
  have eq39160 : x = (M.op x (σ y)) := by
    first
    | (have i₁ := eq36860
       have i₂ := eq31049 sF3
       grind)
    | exact superpose eq31049 eq36860
    | exact resolve eq36860 eq31049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31049 eq36860
  have eq39161 : x = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq31724 eq39160
    | exact resolve eq39160 eq31724
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31724 eq39160
  have eq39537 : x ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq39161 eq28
    | exact resolve eq28 eq39161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq39161
  have eq39555 : False := by grind
  exact eq39555

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pxy_y_pxy_y_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X1 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
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
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X1 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61 : (k x y) = (τ (k (σ x) (σ y))) := by
    first
    | (have i₁ := eq16 (k x y)
       have i₂ := eq45
       grind)
    | exact superpose eq45 eq16
    | exact resolve eq16 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 (M.op X0 X2))) X1) = (M.op (M.op X0 (M.op X1 (M.op X0 X2))) X1) := by
    intro X0 X1 X2
    grind
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq80 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X1 X2)) ∨ (M.op (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) = X1 ∨ (M.op X0 (M.op X1 X2)) = (k X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 (M.op X0 (M.op X1 X2))
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 (M.op X0 (M.op X1 X2))
       grind)
    | (have r₁ := eq12 X1 (M.op (M.op X1 X2) (M.op X1 X2))
       have r₂ := eq14 (M.op X1 X2) X1 X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq104 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq115 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
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
  have eq117 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq115
    | exact resolve eq115 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq118 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq117
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq117
    | exact resolve eq117 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq213 : ∀ X0 : G, (M.op (M.op x (M.op X0 (M.op x y))) X0) = (k (M.op x (M.op X0 (M.op x y))) X0) := by
    intro X0
    grind
  have eq242 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 x X0
       have i₂ := eq56 x X1
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq250 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1127 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) X1) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq67 x X1 (M.op X0 (M.op X1 (M.op X0 x)))
       have i₂ := eq54 X0 X1 x x
       grind)
    | exact superpose eq54 eq67
    | exact resolve eq67 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq67
  have eq1155 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1127 X0 X1
       have i₂ := eq250 X0 X0
       grind)
    | exact superpose eq250 eq1127
    | exact resolve eq1127 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1127
  have eq1329 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 X0
       have i₂ := eq56 X0 (σ X0)
       grind)
    | exact superpose eq56 eq96
    | exact resolve eq96 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1344 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1 (σ X0)
       have i₂ := eq96 X0 X0
       grind)
    | exact superpose eq96 eq56
    | (have j1 := eq96 X0 X0
       grind)
    | exact resolve eq56 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1362 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq96 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq1363 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1362 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1362
  have eq1373 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1344 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1344
  have eq1388 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1329 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1329
  have eq1395 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1373 X0 X1
       have i₂ := eq250 X1 X1
       grind)
    | exact superpose eq250 eq1373
    | (have j0 := eq1373 X0 X1
       grind)
    | exact resolve eq1373 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1373
  have eq1397 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1388 X0 X1
       have i₂ := eq250 X0 X0
       grind)
    | exact superpose eq250 eq1388
    | (have j0 := eq1388 X0 X1
       grind)
    | exact resolve eq1388 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1388
  have eq1414 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1397 X0 X1
       have i₂ := eq250 X0 X0
       grind)
    | exact superpose eq250 eq1397
    | (have j0 := eq1397 X0 X1
       grind)
    | exact resolve eq1397 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1397
  have eq1453 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X0 (M.op X1 X2)) ∨ (M.op x (M.op (M.op X0 (M.op X1 X2)) (M.op x y))) = X1 ∨ (M.op X0 (M.op X1 X2)) = (k X1 (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq80 X0 X1 X2
       have i₂ := eq52 (M.op X0 (M.op X1 X2))
       grind)
    | exact superpose eq52 eq80
    | (have j0 := eq80 X0 X1 X2
       grind)
    | (have r₁ := eq80 x x (M.op x y)
       have r₂ := eq52 x
       grind)
    | exact resolve eq80 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80
  have eq1527 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op (σ x) (σ x)) ∨ (M.op x (M.op (M.op X0 X0) (M.op x y))) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq53 eq1453
    | (have r₁ := eq1453 (σ x) (σ x) (M.op (σ x) (σ y))
       have r₂ := eq53 (σ x)
       grind)
    | exact resolve eq1453 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1453
  have eq1544 : ∀ X0 : G, (M.op x (M.op (M.op X0 X0) (M.op x y))) = X0 ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq1527 X0
       grind)
    | (have r₁ := eq1527 X0
       have r₂ := eq242 X0 (σ x)
       grind)
    | (have r₁ := eq1527 x
       have r₂ := eq242 (σ x) x
       grind)
    | exact resolve eq1527 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1527
  have eq10206 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1363 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq1363
    | (have j0 := eq1363 (τ X0)
       grind)
    | exact resolve eq1363 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1363
  have eq10214 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq10206 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10206
    | (have j0 := eq10206 X0
       grind)
    | exact resolve eq10206 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10206
  have eq10223 : ∀ X0 : G, (σ (τ X0)) = (M.op x (M.op (σ (τ X0)) (M.op x y))) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq10214 X0
       have i₂ := eq52 (σ (τ X0))
       grind)
    | exact superpose eq52 eq10214
    | (have j0 := eq10214 X0
       grind)
    | exact resolve eq10214 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10214
  have eq10228 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op x (M.op X0 (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq10223 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq10223
    | (have j0 := eq10223 X0
       grind)
    | exact resolve eq10223 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10223
  have eq10350 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ (k x x)) := by
    intro X0
    first
    | (have i₁ := eq1395 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1395
    | (have j0 := eq1395 x X0
       grind)
    | exact resolve eq1395 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10351 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ (k y y)) := by
    intro X0
    first
    | (have i₁ := eq1395 y X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1395
    | (have j0 := eq1395 y X0
       grind)
    | exact resolve eq1395 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1395
  have eq10454 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq10351 X0
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq10351
    | exact resolve eq10351 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq10351
  have eq10455 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10350 X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq10350
    | exact resolve eq10350 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq10350
  have eq10912 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (σ y) = (M.op x (M.op (σ y) (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq10454 eq10228
    | (have j0 := eq10228 (σ y)
       grind)
    | exact resolve eq10228 eq10454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10454
  have eq10924 : ∀ X0 : G, (σ y) = (M.op (σ y) (σ y)) ∨ (M.op X0 X0) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq52 eq10912
    | (have j0 := eq10912 X0
       grind)
    | exact resolve eq10912 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10912
  have eq10925 : ∀ X0 : G, (M.op X0 X0) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq10924 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10924
  have eq11151 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op x (M.op (σ x) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq10455 eq10228
    | (have j0 := eq10228 (σ x)
       grind)
    | exact resolve eq10228 eq10455
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10228 eq10455
  have eq11163 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq52 eq11151
    | (have j0 := eq11151 X0
       grind)
    | exact resolve eq11151 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11151
  have eq11164 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq11163 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11163
  have eq12738 : ∀ X0 : G, (M.op X0 (M.op X0 X0)) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq1544 eq213
    | (have j1 := eq1544 X0
       grind)
    | exact resolve eq213 eq1544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq1544
  have eq12776 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) ∨ (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq12738 X0
       have i₂ := eq250 X0 X0
       grind)
    | exact superpose eq250 eq12738
    | (have j0 := eq12738 X0
       grind)
    | exact resolve eq12738 eq250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq250 eq12738
  have eq12777 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq12776 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12776
  have eq12810 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12777 X0
       have i₂ := eq242 X0 X1
       grind)
    | (have i₁ := eq12777 X1
       have i₂ := eq242 X0 X1
       grind)
    | exact superpose eq242 eq12777
    | exact resolve eq12777 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12777
  have eq12962 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) ∨ (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1414 X1 (M.op X0 X0)
       have i₂ := eq12810 X0 (M.op X0 X0)
       grind)
    | exact superpose eq12810 eq1414
    | (have j0 := eq1414 X1 (M.op X0 X0)
       grind)
    | exact resolve eq1414 eq12810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1414 eq12810
  have eq12978 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq12962 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12962
  have eq13055 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op x (M.op X0 (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq12978 X0 X1
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq12978
    | exact resolve eq12978 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13150 : ∀ X0 : G, (σ x) ≠ (σ (M.op X0 X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq11164 x
       have i₂ := eq12978 X0 x
       grind)
    | exact superpose eq12978 eq11164
    | exact resolve eq11164 eq12978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13164 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 x) X1 x
       have i₂ := eq12978 X0 (M.op X1 x)
       grind)
    | exact superpose eq12978 eq14
    | exact resolve eq14 eq12978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13203 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X1 X1)
       have i₂ := eq12978 X1 X0
       grind)
    | exact superpose eq12978 eq16
    | exact resolve eq16 eq12978
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12978
  have eq13473 : ∀ X0 X1 : G, (τ (M.op X0 X0)) = (M.op X1 (τ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 x) X1 x
       have i₂ := eq13203 X0 (M.op X1 x)
       grind)
    | exact superpose eq13203 eq14
    | exact resolve eq14 eq13203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13203
  have eq59614 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq118 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq118
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118
  have eq59622 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq59614
    | exact resolve eq59614 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59614
  have eq59633 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq59622
       have r₂ := eq28
       grind)
    | exact resolve eq59622 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59622
  have eq59635 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq59633
    | exact resolve eq59633 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59633
  have eq59637 : ∀ X0 : G, x = (M.op y y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq59635
       have i₂ := eq242 sF3 x
       grind)
    | (have i₁ := eq59635
       have i₂ := eq242 X0 sF3
       grind)
    | exact superpose eq242 eq59635
    | exact resolve eq59635 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59635
  have eq59824 : ∀ X0 : G, (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op X0 X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq13150 y
       have i₂ := eq59637 X0
       grind)
    | exact superpose eq59637 eq13150
    | (have j1 := eq59637 (σ x)
       grind)
    | exact resolve eq13150 eq59637
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13150 eq59637
  have eq59910 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have j0 := eq59824 (σ x)
       grind)
    | (have r₁ := eq59824 x
       have r₂ := eq11164 (σ x)
       grind)
    | (have r₁ := eq59824 x
       have r₂ := eq11164 x
       grind)
    | exact resolve eq59824 eq11164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11164 eq59824
  have eq59924 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq59910
       have r₂ := eq23
       grind)
    | exact resolve eq59910 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq59910
  have eq60154 : ∀ X0 : G, (k (σ x) X0) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq59924 eq1155
    | exact resolve eq1155 eq59924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq60186 : ∀ X0 : G, (τ (σ x)) = (M.op X0 (τ (σ x))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq59924 eq13473
    | exact resolve eq13473 eq59924
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59924
  have eq60260 : ∀ X0 : G, x = (M.op X0 x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq60186
    | exact resolve eq60186 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq60186
  have eq61440 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq1155 x x
       have i₂ := eq60260 x
       grind)
    | exact superpose eq60260 eq1155
    | exact resolve eq1155 eq60260
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1155 eq60260
  have eq69378 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq60154 eq61
    | exact resolve eq61 eq60154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq60154
  have eq69402 : (k x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq69378
    | exact resolve eq69378 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69378
  have eq83897 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq69402
       have i₂ := eq61440 y
       grind)
    | exact superpose eq61440 eq69402
    | exact resolve eq69402 eq61440
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61440 eq69402
  have eq83911 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq83897
  have eq83919 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq83911
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq83911
    | exact resolve eq83911 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83911
  have eq83979 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq83919 eq15
    | exact resolve eq15 eq83919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83919
  have eq84031 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq21 eq83979
    | exact resolve eq83979 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83979
  have eq84032 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq84031
       have r₂ := eq28
       grind)
    | exact resolve eq84031 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84031
  have eq84034 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ x) (M.op X0 (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq84032 eq53
    | exact resolve eq53 eq84032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq84608 : (M.op (σ x) (σ x)) = (M.op (σ x) (M.op (σ x) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq84034
    | (have j0 := eq84034 (σ x)
       grind)
    | exact resolve eq84034 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84034
  have eq85103 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq84032 eq84608
    | exact resolve eq84608 eq84032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84608
  have eq85129 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq85103
  have eq85131 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq27 eq85129
    | exact resolve eq85129 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85129
  have eq85183 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq85131 eq10925
    | exact resolve eq10925 eq85131
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10925 eq85131
  have eq85345 : (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq85183
       have r₂ := eq84032
       grind)
    | exact resolve eq85183 eq84032
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84032 eq85183
  have eq86145 : ∀ X0 : G, (τ (σ y)) = (M.op X0 (τ (σ y))) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq85345 eq13473
    | exact resolve eq13473 eq85345
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13473 eq85345
  have eq86282 : ∀ X0 : G, y = (M.op X0 y) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq30 eq86145
    | exact resolve eq86145 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq86145
  have eq87585 : y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq19
       have i₂ := eq86282 x
       grind)
    | exact superpose eq86282 eq19
    | (have j1 := eq86282 x
       grind)
    | exact resolve eq19 eq86282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86282
  have eq87588 : y = (M.op x y) := by grind
  clear eq87585
  have eq87653 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq87588 eq21
    | exact resolve eq21 eq87588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87655 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 y)) := by
    intro X0
    first
    | exact superpose eq87588 eq52
    | exact resolve eq52 eq87588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq87816 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq87653
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq87653
    | exact resolve eq87653 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87653
  have eq87818 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq87816 eq27
    | exact resolve eq27 eq87816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq92238 : (M.op x x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq87655 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq87655
    | (have j0 := eq87655 x
       grind)
    | exact resolve eq87655 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87655
  have eq92722 : (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq87588 eq92238
    | exact resolve eq92238 eq87588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92238
  have eq92784 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq92722
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq92722
    | exact resolve eq92722 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92722
  have eq92798 : y = (M.op x x) := by
    first
    | exact superpose eq87588 eq92784
    | exact resolve eq92784 eq87588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87588 eq92784
  have eq92804 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq92798
       have i₂ := eq242 x X0
       grind)
    | (have i₁ := eq92798
       have i₂ := eq242 X0 x
       grind)
    | exact superpose eq242 eq92798
    | exact resolve eq92798 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242
  have eq92868 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq13164 x x
       have i₂ := eq92798
       grind)
    | exact superpose eq92798 eq13164
    | exact resolve eq13164 eq92798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13164 eq92798
  have eq92983 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq92868 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq92868
    | (have j0 := eq92868 X0
       grind)
    | exact resolve eq92868 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq92868
  have eq93015 : ∀ X0 : G, (σ (M.op x y)) = (M.op X0 (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq87816 eq92983
    | exact resolve eq92983 eq87816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87816 eq92983
  have eq94022 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq13055 sF0 x
       have i₂ := eq92804 sF0
       grind)
    | exact superpose eq92804 eq13055
    | exact resolve eq13055 eq92804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13055
  have eq94099 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq94022 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq94022
    | (have j0 := eq94022 X0
       grind)
    | exact resolve eq94022 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq94022
  have eq94417 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq94099
    | (have j0 := eq94099 X0
       grind)
    | exact resolve eq94099 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq94099
  have eq94579 : y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq94417 x
       have i₂ := eq92804 x
       grind)
    | exact superpose eq92804 eq94417
    | exact resolve eq94417 eq92804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92804 eq94417
  have eq94760 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq94579 eq87818
    | exact resolve eq87818 eq94579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87818
  have eq98508 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq94579 eq93015
    | exact resolve eq93015 eq94579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93015
  have eq100434 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq94760
       have i₂ := eq98508 sF2
       grind)
    | exact superpose eq98508 eq94760
    | exact resolve eq94760 eq98508
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94760 eq98508
  have eq100437 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq100434 eq28
    | exact resolve eq28 eq100434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq100434
  have eq100456 : False := by grind
  exact eq100456

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(X,Y) else if m(Y,X) = X then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_pyx_x_pxy_pyx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ M.op b a = a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  clear eq25 eq36
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
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
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X1 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (k (M.op X0 (M.op X1 (M.op X0 X2))) X1) = (M.op (M.op X0 (M.op X1 (M.op X0 X2))) X1) := by
    intro X0 X1 X2
    grind
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq84
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq92
    | exact resolve eq92 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq240 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 x X0
       have i₂ := eq56 x X1
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq411 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 X1 X2
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq1109 : ∀ X0 X1 : G, (k (M.op X0 (M.op X0 X0)) X1) = (M.op (M.op X0 (M.op X0 X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq67 x X1 (M.op X0 (M.op X1 (M.op X0 x)))
       have i₂ := eq54 X0 X1 x x
       grind)
    | exact superpose eq54 eq67
    | exact resolve eq67 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq67
  have eq1137 : ∀ X0 X1 : G, (k (M.op X0 X0) X1) = (M.op (M.op X0 X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1109 X0 X1
       have i₂ := eq248 X0 X0
       grind)
    | exact superpose eq248 eq1109
    | exact resolve eq1109 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1109
  have eq1310 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X0
       have i₂ := eq56 X0 (σ X0)
       grind)
    | exact superpose eq56 eq77
    | exact resolve eq77 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1325 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq56 X1 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq56
    | (have j1 := eq77 X0 X0
       grind)
    | exact resolve eq56 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1343 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq77 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1344 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1343 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1343
  have eq1354 : ∀ X0 X1 : G, (M.op X1 (M.op X1 X1)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1325 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq1369 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1310 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1310
  have eq1376 : ∀ X0 X1 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1354 X0 X1
       have i₂ := eq248 X1 X1
       grind)
    | exact superpose eq248 eq1354
    | (have j0 := eq1354 X0 X1
       grind)
    | exact resolve eq1354 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1354
  have eq1378 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1369 X0 X1
       have i₂ := eq248 X0 X0
       grind)
    | exact superpose eq248 eq1369
    | (have j0 := eq1369 X0 X1
       grind)
    | exact resolve eq1369 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1369
  have eq1394 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1378 X0 X1
       have i₂ := eq248 X0 X0
       grind)
    | exact superpose eq248 eq1378
    | (have j0 := eq1378 X0 X1
       grind)
    | exact resolve eq1378 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq1378
  have eq5612 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq1394 X0 (τ X1)
       grind)
    | exact superpose eq1394 eq35
    | (have j1 := eq1394 X0 (τ X1)
       grind)
    | exact resolve eq35 eq1394
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1394
  have eq5643 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5612 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5612
    | (have j0 := eq5612 X0 X1
       grind)
    | exact resolve eq5612 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5612
  have eq5703 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq5643 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq5643
    | (have j0 := eq5643 X0 X1
       grind)
    | exact resolve eq5643 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5643
  have eq8247 : ∀ X0 : G, (k (σ x) (σ x)) = (σ (M.op X0 X0)) ∨ (M.op X0 X0) = x := by
    intro X0
    first
    | (have i₁ := eq44
       have i₂ := eq5703 X0 x
       grind)
    | exact superpose eq5703 eq44
    | (have j1 := eq5703 X0 x
       grind)
    | exact resolve eq44 eq5703
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9972 : ∀ X0 : G, (σ (τ X0)) ≠ (k X0 (σ (τ X0))) ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq1344 (τ X0)
       have i₂ := eq35 X0 (τ X0)
       grind)
    | exact superpose eq35 eq1344
    | (have j0 := eq1344 (τ X0)
       grind)
    | exact resolve eq1344 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1344
  have eq9980 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (σ (τ X0)) = (M.op (σ (τ X0)) (σ (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq9972 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq9972
    | (have j0 := eq9972 X0
       grind)
    | exact resolve eq9972 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9972
  have eq9989 : ∀ X0 : G, (σ (τ X0)) = (M.op x (M.op (σ (τ X0)) (M.op x y))) ∨ (k X0 X0) ≠ X0 := by
    intro X0
    first
    | (have i₁ := eq9980 X0
       have i₂ := eq52 (σ (τ X0))
       grind)
    | exact superpose eq52 eq9980
    | (have j0 := eq9980 X0
       grind)
    | exact resolve eq9980 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9980
  have eq9994 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op x (M.op X0 (M.op x y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq9989 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq9989
    | (have j0 := eq9989 X0
       grind)
    | exact resolve eq9989 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9989
  have eq10204 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) = (σ (k x x)) := by
    intro X0
    first
    | (have i₁ := eq1376 x X0
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq1376
    | (have j0 := eq1376 x X0
       grind)
    | exact resolve eq1376 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1376
  have eq10309 : ∀ X0 : G, (M.op X0 X0) = (k (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq10204 X0
       have i₂ := eq44
       grind)
    | exact superpose eq44 eq10204
    | exact resolve eq10204 eq44
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10204
  have eq11005 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op x (M.op (σ x) (M.op x y))) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq10309 eq9994
    | (have j0 := eq9994 (σ x)
       grind)
    | exact resolve eq9994 eq10309
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9994 eq10309
  have eq11017 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ x)) ∨ (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | exact superpose eq52 eq11005
    | (have j0 := eq11005 X0
       grind)
    | exact resolve eq11005 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq11005
  have eq11018 : ∀ X0 : G, (M.op X0 X0) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have j0 := eq11017 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11017
  have eq43958 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq93 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq93
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43966 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq43958
    | exact resolve eq43958 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43958
  have eq43977 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq43966
       have r₂ := eq28
       grind)
    | exact resolve eq43966 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43966
  have eq43982 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq43977
  have eq44062 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq43982
    | exact resolve eq43982 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43982
  have eq44095 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq44062 eq93
    | exact resolve eq93 eq44062
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq44062
  have eq44111 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ x)) := by grind
  clear eq44095
  have eq44114 : (σ x) = (M.op (σ y) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq44111
       have r₂ := eq28
       grind)
    | exact resolve eq44111 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44111
  have eq44117 : ∀ X0 : G, (M.op X0 X0) = (M.op (σ y) (M.op X0 (σ x))) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    intro X0
    first
    | exact superpose eq44114 eq14
    | exact resolve eq14 eq44114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44205 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq44114 eq44117
    | exact resolve eq44117 eq44114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44117
  have eq44428 : (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq44205
  have eq44527 : (σ x) ≠ (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq44428 eq11018
    | exact resolve eq11018 eq44428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11018 eq44428
  have eq44558 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq44527
       have r₂ := eq44114
       grind)
    | exact resolve eq44527 eq44114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44527
  have eq44562 : (k (σ x) (σ x)) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  have eq44571 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    intro X0 X1
    first
    | exact superpose eq44558 eq411
    | exact resolve eq411 eq44558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq411
  have eq46225 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq44558
       have i₂ := eq44571 sF2 x
       grind)
    | exact superpose eq44571 eq44558
    | exact resolve eq44558 eq44571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44558
  have eq46307 : ∀ X0 : G, x ≠ (M.op X0 (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    intro X0
    grind
  clear eq44571
  have eq46318 : ∀ X0 : G, (σ x) = (M.op X0 (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have j0 := eq46225 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46225
  have eq46409 : x ≠ (σ x) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq44114 eq46307
    | exact resolve eq46307 eq44114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44114 eq46307
  have eq46412 : x ≠ (σ x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq46409
  have eq46456 : (k (σ x) (σ x)) = (σ (σ x)) ∨ x = (σ x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq46318 eq8247
    | (have j0 := eq8247 y
       grind)
    | exact resolve eq8247 eq46318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8247
  have eq46518 : (k (σ x) (σ x)) = (σ (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | (have r₁ := eq46456
       have r₂ := eq46412
       grind)
    | exact resolve eq46456 eq46412
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46456
  have eq46648 : (M.op (σ x) (σ x)) = (σ (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq46518 eq44562
    | exact resolve eq44562 eq46518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44562 eq46518
  have eq46679 : (M.op (σ x) (σ x)) = (σ (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq46648
  have eq46788 : (σ x) = (σ (σ x)) ∨ x = (M.op y y) ∨ x = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq46679 eq46318
    | exact resolve eq46318 eq46679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46318 eq46679
  have eq46866 : x = (M.op y y) ∨ (σ x) = (σ (σ x)) ∨ x = (M.op y x) := by grind
  clear eq46788
  have eq46900 : ∀ X0 : G, (M.op X0 X0) = (M.op y x) ∨ (σ x) = (σ (σ x)) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq56 y X0
       have i₂ := eq46866
       grind)
    | exact superpose eq46866 eq56
    | exact resolve eq56 eq46866
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47910 : x = (M.op y x) ∨ (σ x) = (σ (σ x)) ∨ x = (M.op y x) ∨ (σ x) = (σ (σ x)) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq46866
       have i₂ := eq46900 y
       grind)
    | exact superpose eq46900 eq46866
    | exact resolve eq46866 eq46900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46866 eq46900
  have eq47952 : x = (M.op y x) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq47910
  have eq48042 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op X0 x)) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq47952
       grind)
    | exact superpose eq47952 eq14
    | exact resolve eq14 eq47952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48138 : (M.op y x) = (M.op y y) ∨ (σ x) = (σ (σ x)) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq48042 y
       have i₂ := eq47952
       grind)
    | exact superpose eq47952 eq48042
    | exact resolve eq48042 eq47952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48042
  have eq48372 : (M.op y x) = (M.op y y) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq48138
  have eq48433 : ∀ X0 : G, (M.op X0 X0) = (M.op y x) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq48372
       have i₂ := eq240 y X0
       grind)
    | (have i₁ := eq48372
       have i₂ := eq240 X0 y
       grind)
    | exact superpose eq240 eq48372
    | exact resolve eq48372 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq48372
  have eq48813 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ x) = (σ (σ x)) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have i₁ := eq47952
       have i₂ := eq48433 X0
       grind)
    | exact superpose eq48433 eq47952
    | exact resolve eq47952 eq48433
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47952 eq48433
  have eq48839 : ∀ X0 : G, (M.op X0 X0) = x ∨ (σ x) = (σ (σ x)) := by
    intro X0
    first
    | (have j0 := eq48813 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48813
  have eq48988 : ∀ X0 : G, (k x X0) = (M.op x X0) ∨ (σ x) = (σ (σ x)) := by
    intro X0
    grind
  have eq49039 : ∀ X1 : G, x = (k X1 X1) ∨ x = X1 ∨ (σ x) = (σ (σ x)) := by
    intro X1
    first
    | (have i₁ := eq5703 x X1
       have i₂ := eq48839 x
       grind)
    | exact superpose eq48839 eq5703
    | exact resolve eq5703 eq48839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5703
  have eq50389 : (k (σ x) (σ x)) = (σ (M.op x x)) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq44
       have i₂ := eq48988 x
       grind)
    | exact superpose eq48988 eq44
    | exact resolve eq44 eq48988
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44 eq48988
  have eq54054 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ (σ x)) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq50389
       have i₂ := eq48839 x
       grind)
    | exact superpose eq48839 eq50389
    | exact resolve eq50389 eq48839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48839 eq50389
  have eq54148 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ (σ x)) := by grind
  clear eq54054
  have eq54204 : (σ x) = (k (σ x) (σ x)) ∨ (σ x) = (σ (σ x)) := by
    first
    | (have i₁ := eq54148
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq54148
    | exact resolve eq54148 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq54148
  have eq54267 : x = (σ x) ∨ x = (σ x) ∨ (σ x) = (σ (σ x)) ∨ (σ x) = (σ (σ x)) := by
    first
    | exact superpose eq54204 eq49039
    | (have j0 := eq49039 (σ x)
       grind)
    | exact resolve eq49039 eq54204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49039 eq54204
  have eq54282 : (σ x) = (σ (σ x)) ∨ x = (σ x) := by grind
  clear eq54267
  have eq54318 : (σ x) = (τ (σ x)) ∨ x = (σ x) := by
    first
    | exact superpose eq54282 eq16
    | exact resolve eq16 eq54282
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54282
  have eq54399 : x = (σ x) ∨ x = (σ x) := by
    first
    | exact superpose eq29 eq54318
    | exact resolve eq54318 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq54318
  have eq54400 : x = (σ x) := by grind
  clear eq54399
  have eq54405 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq54400 eq27
    | exact resolve eq27 eq54400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq54495 : x ≠ x ∨ x = (M.op y y) ∨ x = (M.op y x) := by
    first
    | exact superpose eq54400 eq46412
    | (have r₁ := eq46412
       have r₂ := eq54400
       grind)
    | exact resolve eq46412 eq54400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46412
  have eq54505 : x = (M.op y y) ∨ x = (M.op y x) := by grind
  clear eq54495
  have eq56581 : ∀ X0 : G, (M.op X0 X0) = (M.op y x) ∨ x = (M.op y x) := by
    intro X0
    first
    | (have i₁ := eq56 y X0
       have i₂ := eq54505
       grind)
    | exact superpose eq54505 eq56
    | exact resolve eq56 eq54505
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq66093 : x = (M.op y x) ∨ x = (M.op y x) ∨ x = (M.op y x) := by
    first
    | (have i₁ := eq54505
       have i₂ := eq56581 y
       grind)
    | exact superpose eq56581 eq54505
    | exact resolve eq54505 eq56581
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54505 eq56581
  have eq66153 : x = (M.op y x) := by grind
  clear eq66093
  have eq66317 : ∀ X0 : G, (M.op X0 X0) = (M.op y (M.op X0 x)) := by
    intro X0
    first
    | (have i₁ := eq14 X0 y x
       have i₂ := eq66153
       grind)
    | exact superpose eq66153 eq14
    | exact resolve eq14 eq66153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq66798 : (M.op y x) = (M.op y y) := by
    first
    | (have i₁ := eq66317 y
       have i₂ := eq66153
       grind)
    | exact superpose eq66153 eq66317
    | exact resolve eq66317 eq66153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66317
  have eq67119 : x = (M.op y y) := by
    first
    | (have i₁ := eq66798
       have i₂ := eq66153
       grind)
    | exact superpose eq66153 eq66798
    | exact resolve eq66798 eq66153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66153 eq66798
  have eq67195 : (M.op x y) = (k x y) := by grind
  have eq67212 : ∀ X0 : G, (k x X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq1137 y x
       have i₂ := eq67119
       grind)
    | exact superpose eq67119 eq1137
    | exact resolve eq1137 eq67119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1137 eq67119
  have eq67298 : (M.op x y) = (k x y) := by
    first
    | (have i₁ := eq67195
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq67195
    | exact resolve eq67195 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq67195
  have eq68065 : (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have i₁ := eq45
       have i₂ := eq67298
       grind)
    | exact superpose eq67298 eq45
    | exact resolve eq45 eq67298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq67298
  have eq68098 : (σ (M.op x y)) = (k x (σ y)) := by
    first
    | exact superpose eq54400 eq68065
    | exact resolve eq68065 eq54400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54400 eq68065
  have eq68114 : (σ (M.op x y)) = (k x (σ y)) := by
    first
    | exact superpose eq21 eq68098
    | exact resolve eq68098 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq68098
  have eq70749 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq68114
       have i₂ := eq67212 sF3
       grind)
    | exact superpose eq67212 eq68114
    | exact resolve eq68114 eq67212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67212 eq68114
  have eq70750 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq54405 eq70749
    | exact resolve eq70749 eq54405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54405 eq70749
  have eq70874 : False := by grind
  exact eq70874

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,X) else if m(X,X) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pxx_pyy_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  clear eq23
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
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
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
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X1 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ X1 ∨ (M.op X3 X3) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X3 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X3 X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq84
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq92
    | exact resolve eq92 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq105 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq16
    | exact resolve eq16 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq253 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 x X0
       have i₂ := eq56 x X1
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 X1 X2
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq721 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X2 X2) = (k X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X1 X1)
       have i₂ := eq430 X1 X0 (M.op X1 X1)
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq430 X0 X1 X2
       grind)
    | exact superpose eq430 eq13
    | (have j0 := eq13 X2 (M.op X1 X1)
       grind)
    | (have r₁ := eq13 X0 (M.op X2 (M.op X0 X0))
       have r₂ := eq430 X0 (M.op X2 (M.op X0 X0)) X2
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq430 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq740 : ∀ X1 X2 : G, (M.op X2 X2) = (k X2 (M.op X1 X1)) := by
    intro X1 X2
    first
    | (have j0 := eq721 x X1 X2
       grind)
    | (have r₁ := eq721 x X1 X2
       have r₂ := eq253 x X1
       grind)
    | (have r₁ := eq721 X1 x X2
       have r₂ := eq253 x X1
       grind)
    | exact resolve eq721 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq974 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (M.op X4 X4) = (k X4 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq67 X0 X1 (M.op x (M.op X1 (M.op x x))) X4
       have i₂ := eq54 x X1 x X0
       grind)
    | exact superpose eq54 eq67
    | (have j0 := eq67 X0 X1 x X4
       grind)
    | exact resolve eq67 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq67
  have eq1004 : ∀ X0 X1 X4 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X4 X4) = (k X4 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq974 X0 X1 X4
       have i₂ := eq262 X0 X0
       grind)
    | exact superpose eq262 eq974
    | (have j0 := eq974 X0 X1 X4
       grind)
    | (have r₁ := eq974 X0 (M.op X0 X0) X4
       have r₂ := eq262 X0 X0
       grind)
    | exact resolve eq974 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq974
  have eq1254 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X0
       have i₂ := eq56 X0 (σ X0)
       grind)
    | exact superpose eq56 eq77
    | exact resolve eq77 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq1261 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq13
    | (have j0 := eq13 X1 (σ X0)
       have j1 := eq77 X0 X0
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq77 X1 X1
       grind)
    | (have r₁ := eq13 X0 (σ X1)
       have r₂ := eq77 X0 X1
       grind)
    | exact resolve eq13 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1264 : ∀ X0 : G, (M.op x (M.op (σ X0) (M.op x y))) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq52 (σ X0)
       have i₂ := eq77 X0 X0
       grind)
    | exact superpose eq77 eq52
    | (have j1 := eq77 X0 X0
       grind)
    | exact resolve eq52 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq1306 : ∀ X0 : G, (M.op x (M.op (σ X0) (M.op x y))) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1264 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1264
  have eq1309 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1261 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1261
  have eq1316 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1254 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1254
  have eq1325 : ∀ X0 X1 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (M.op X1 X1) = (k X1 (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1309 X0 X1
       have j1 := eq13 X1 (σ X0)
       grind)
    | (have r₁ := eq1309 X0 X1
       have r₂ := eq13 X0 (σ X0)
       grind)
    | exact resolve eq1309 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1309
  have eq1326 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1316 X0 X1
       have i₂ := eq262 X0 X0
       grind)
    | exact superpose eq262 eq1316
    | (have j0 := eq1316 X0 X1
       grind)
    | exact resolve eq1316 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1316
  have eq1356 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1326 X0 X1
       have i₂ := eq262 X0 X0
       grind)
    | exact superpose eq262 eq1326
    | (have j0 := eq1326 X0 X1
       grind)
    | exact resolve eq1326 eq262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq262 eq1326
  have eq1522 : ∀ X0 X1 : G, (M.op x (M.op X0 (M.op x y))) = (k X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq740 X1 X0
       have i₂ := eq52 X0
       grind)
    | exact superpose eq52 eq740
    | exact resolve eq740 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1527 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X1 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq740 X2 X1
       have i₂ := eq253 X1 X0
       grind)
    | (have i₁ := eq740 X2 X1
       have i₂ := eq253 X0 X1
       grind)
    | exact superpose eq253 eq740
    | exact resolve eq740 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1706 : ∀ X0 X1 X2 : G, (k X1 (σ (M.op X2 X2))) = (σ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq35 X1 (M.op X2 X2)
       have i₂ := eq1527 X0 (τ X1) X2
       grind)
    | exact superpose eq1527 eq35
    | exact resolve eq35 eq1527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1527
  have eq7298 : ∀ X0 X3 : G, (σ (M.op X0 X0)) = (σ (M.op X3 X3)) := by
    intro X0 X3
    first
    | (have i₁ := eq1706 X3 x x
       have i₂ := eq1706 X0 x x
       grind)
    | exact superpose eq1706 eq1706
    | exact resolve eq1706 eq1706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8472 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq1356 X0 (τ X1)
       grind)
    | exact superpose eq1356 eq35
    | (have j1 := eq1356 X0 (τ X1)
       grind)
    | exact resolve eq35 eq1356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq1356
  have eq8502 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq8472 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq8472
    | (have j0 := eq8472 X0 X1
       grind)
    | exact resolve eq8472 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8472
  have eq8582 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq8502 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq8502
    | (have j0 := eq8502 X0 X1
       grind)
    | exact resolve eq8502 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8502
  have eq10856 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op (M.op X0 X0) (M.op X0 X0))) ∨ (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq1325 (M.op X0 X0) X1
       have i₂ := eq740 X0 (M.op X0 X0)
       grind)
    | exact superpose eq740 eq1325
    | (have j0 := eq1325 (M.op X0 X0) X1
       grind)
    | exact resolve eq1325 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1325
  have eq10883 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have j0 := eq10856 X0 X1
       grind)
    | (have r₁ := eq10856 X0 X1
       have r₂ := eq7298 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq10856 x X1
       have r₂ := eq7298 (M.op x x) x
       grind)
    | exact resolve eq10856 eq7298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7298 eq10856
  have eq10903 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X1 (σ (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10883 X2 X1
       have i₂ := eq253 X1 X0
       grind)
    | (have i₁ := eq10883 X2 X1
       have i₂ := eq253 X0 X1
       grind)
    | exact superpose eq253 eq10883
    | exact resolve eq10883 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10984 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10883 x X1
       have i₂ := eq1706 X0 X1 x
       grind)
    | exact superpose eq1706 eq10883
    | exact resolve eq10883 eq1706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1706
  have eq11115 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq38 (M.op X0 X0)
       have i₂ := eq10883 X0 sF1
       grind)
    | exact superpose eq10883 eq38
    | exact resolve eq38 eq10883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq11116 : ∀ X0 : G, (M.op (σ x) (σ x)) = (σ (k x (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq36 (M.op X0 X0)
       have i₂ := eq10883 X0 sF2
       grind)
    | exact superpose eq10883 eq36
    | exact resolve eq36 eq10883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq11117 : ∀ X0 : G, (M.op (σ y) (σ y)) = (σ (k y (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq37 (M.op X0 X0)
       have i₂ := eq10883 X0 sF3
       grind)
    | exact superpose eq10883 eq37
    | exact resolve eq37 eq10883
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq10883
  have eq11145 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq11117 x
       have i₂ := eq740 x y
       grind)
    | exact superpose eq740 eq11117
    | exact resolve eq11117 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11117
  have eq11146 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq11116 x
       have i₂ := eq740 x x
       grind)
    | exact superpose eq740 eq11116
    | exact resolve eq11116 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11116
  have eq11147 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq11115 x
       have i₂ := eq740 x sF0
       grind)
    | exact superpose eq740 eq11115
    | exact resolve eq11115 eq740
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq740 eq11115
  have eq11254 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq11145
       grind)
    | exact superpose eq11145 eq16
    | exact resolve eq16 eq11145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11145
  have eq11303 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq16 (M.op x x)
       have i₂ := eq11146
       grind)
    | exact superpose eq11146 eq16
    | exact resolve eq16 eq11146
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11146
  have eq11567 : ∀ X0 X1 : G, (σ (M.op X0 X0)) = (M.op X1 (σ (M.op X0 X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 x) X1 x
       have i₂ := eq10984 X0 (M.op X1 x)
       grind)
    | exact superpose eq10984 eq14
    | exact resolve eq14 eq10984
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10984
  have eq14207 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (σ (k X1 (M.op X2 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 X1 (M.op X2 X2)
       have i₂ := eq10903 X0 (σ X1) X2
       grind)
    | exact superpose eq10903 eq10
    | exact resolve eq10 eq10903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10903
  have eq14241 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (M.op x (M.op X1 (M.op x y)))) := by
    intro X0 X1
    first
    | (have i₁ := eq14207 X0 X1 x
       have i₂ := eq1522 X1 x
       grind)
    | exact superpose eq1522 eq14207
    | exact resolve eq14207 eq1522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1522 eq14207
  have eq20754 : (σ (k y y)) = (M.op x (M.op (σ y) (M.op x y))) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq1306 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq1306
    | (have j0 := eq1306 y
       grind)
    | exact resolve eq1306 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1306
  have eq20878 : (σ (k y y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq52 eq20754
    | exact resolve eq20754 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq20754
  have eq20898 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq20878
       have i₂ := eq75
       grind)
    | exact superpose eq75 eq20878
    | exact resolve eq20878 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq20878
  have eq20907 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have j1 := eq1004 x (σ y) (σ y)
       grind)
    | (have r₁ := eq20898
       have r₂ := eq1004 (σ y) (k (σ y) (σ y)) x
       grind)
    | (have r₁ := eq20898
       have r₂ := eq1004 (σ y) (σ y) x
       grind)
    | exact resolve eq20898 eq1004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1004 eq20898
  have eq20918 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | exact superpose eq20907 eq105
    | exact resolve eq105 eq20907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq20923 : (k y y) = (M.op y y) := by
    first
    | exact superpose eq11254 eq20918
    | exact resolve eq20918 eq11254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11254 eq20918
  have eq55379 : ∀ X0 X1 : G, (k X1 X1) ≠ X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq8582 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8582
  have eq55625 : ∀ X0 : G, y ≠ (M.op y y) ∨ (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq55379 X0 y
       have i₂ := eq20923
       grind)
    | exact superpose eq20923 eq55379
    | (have j0 := eq55379 X0 y
       grind)
    | exact resolve eq55379 eq20923
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20923
  have eq55629 : ∀ X0 : G, (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | exact superpose eq20907 eq55379
    | (have j0 := eq55379 X0 (σ y)
       grind)
    | exact resolve eq55379 eq20907
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20907 eq55379
  have eq55633 : ∀ X0 X1 : G, (M.op X0 X0) ≠ y ∨ (M.op X1 X1) = y := by
    intro X0 X1
    first
    | (have i₁ := eq55625 X1
       have i₂ := eq253 y X0
       grind)
    | (have i₁ := eq55625 X1
       have i₂ := eq253 X0 y
       grind)
    | exact superpose eq253 eq55625
    | (have j0 := eq55625 X1
       grind)
    | exact resolve eq55625 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55625
  have eq55641 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ y) ∨ (M.op X1 X1) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq55629 X0
       have i₂ := eq253 sF3 X1
       grind)
    | (have i₁ := eq55629 X0
       have i₂ := eq253 X0 sF3
       grind)
    | exact superpose eq253 eq55629
    | (have j0 := eq55629 X1
       grind)
    | exact resolve eq55629 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55629
  have eq106013 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq55633 x x
       grind)
    | (have r₁ := eq93
       have r₂ := eq55633 x x
       grind)
    | (have r₁ := eq93
       have r₂ := eq55633 y x
       grind)
    | exact resolve eq93 eq55633
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93 eq55633
  have eq106024 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq106013 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq106013
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106013
  have eq106039 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq55641 x (σ x)
       grind)
    | (have r₁ := eq106024
       have r₂ := eq55641 (σ x) x
       grind)
    | (have r₁ := eq106024
       have r₂ := eq55641 (σ y) x
       grind)
    | exact resolve eq106024 eq55641
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55641 eq106024
  have eq106050 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq106039
    | exact resolve eq106039 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106039
  have eq106054 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq106050
       have r₂ := eq28
       grind)
    | exact resolve eq106050 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106050
  have eq106058 : (τ (σ y)) = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq106054 eq11303
    | exact resolve eq11303 eq106054
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11303 eq106054
  have eq106289 : y = (M.op x x) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq106058
    | exact resolve eq106058 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq106058
  have eq106290 : y = (M.op x x) := by grind
  clear eq106289
  have eq106300 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq106290
       have i₂ := eq253 x X0
       grind)
    | (have i₁ := eq106290
       have i₂ := eq253 X0 x
       grind)
    | exact superpose eq253 eq106290
    | exact resolve eq106290 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq253
  have eq106362 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq11567 x x
       have i₂ := eq106290
       grind)
    | exact superpose eq106290 eq11567
    | exact resolve eq11567 eq106290
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11567 eq106290
  have eq106506 : ∀ X0 : G, (σ y) = (M.op X0 (σ y)) := by
    intro X0
    first
    | (have i₁ := eq106362 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq106362
    | (have j0 := eq106362 X0
       grind)
    | exact resolve eq106362 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106362
  have eq107040 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq14241 X0 sF0
       have i₂ := eq106300 sF0
       grind)
    | exact superpose eq106300 eq14241
    | exact resolve eq14241 eq106300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14241
  have eq107084 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq11147
       have i₂ := eq106300 sF0
       grind)
    | exact superpose eq106300 eq11147
    | exact resolve eq11147 eq106300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11147
  have eq107141 : y = (σ y) := by
    first
    | (have i₁ := eq107084
       have i₂ := eq106300 sF1
       grind)
    | exact superpose eq106300 eq107084
    | exact resolve eq107084 eq106300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107084
  have eq107179 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq107040 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq107040
    | (have j0 := eq107040 X0
       grind)
    | exact resolve eq107040 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq107040
  have eq107548 : y = (σ y) := by
    first
    | (have i₁ := eq107141
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq107141
    | exact resolve eq107141 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq107141
  have eq107580 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | exact superpose eq21 eq107179
    | (have j0 := eq107179 X0
       grind)
    | exact resolve eq107179 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq107179
  have eq107747 : y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq107580 x
       have i₂ := eq106300 x
       grind)
    | exact superpose eq106300 eq107580
    | exact resolve eq107580 eq106300
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106300 eq107580
  have eq108136 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq107548 eq27
    | exact resolve eq27 eq107548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq114571 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq107548 eq106506
    | exact resolve eq106506 eq107548
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106506 eq107548
  have eq115718 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq108136
       have i₂ := eq114571 sF2
       grind)
    | exact superpose eq114571 eq108136
    | exact resolve eq108136 eq114571
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108136 eq114571
  have eq115722 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq115718 eq28
    | exact resolve eq28 eq115718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq115718
  have eq115723 : False := by grind
  exact eq115723

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,X) = Y then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyy_pxx_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  clear eq23
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
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
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
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X1 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ X1 ∨ (M.op X0 (M.op X1 (M.op X0 X2))) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq84
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq92
    | exact resolve eq92 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq137 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq160 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq137 eq16
    | exact resolve eq16 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 x X0
       have i₂ := eq56 x X1
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1071 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (M.op X0 (M.op X0 X0)) = (k X4 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq67 x X1 (M.op X0 (M.op X1 (M.op X0 x))) x
       have i₂ := eq54 X0 X1 x x
       grind)
    | exact superpose eq54 eq67
    | exact resolve eq67 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq67
  have eq1102 : ∀ X0 X1 X4 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 (M.op X0 X0)) = (k X4 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq1071 X0 X1 X4
       have i₂ := eq257 X0 X0
       grind)
    | exact superpose eq257 eq1071
    | (have j0 := eq1071 X0 X1 X4
       grind)
    | (have r₁ := eq1071 X0 (M.op X0 X0) X4
       have r₂ := eq257 X0 X0
       grind)
    | exact resolve eq1071 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1071
  have eq1111 : ∀ X0 X1 X4 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X4 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq1102 X0 X1 X4
       have i₂ := eq257 X0 X0
       grind)
    | exact superpose eq257 eq1102
    | (have j0 := eq1102 X0 X1 X4
       grind)
    | (have r₁ := eq1102 X1 (M.op X1 (M.op X0 X0)) X4
       have r₂ := eq257 X0 X1
       grind)
    | (have r₁ := eq1102 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)) X4
       have r₂ := eq257 X0 (M.op X0 X0)
       grind)
    | exact resolve eq1102 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1102
  have eq1311 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X0
       have i₂ := eq56 X0 (σ X0)
       grind)
    | exact superpose eq56 eq77
    | exact resolve eq77 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq77
  have eq1375 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1311 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1311
  have eq1385 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1375 X0 X1
       have i₂ := eq257 X0 X0
       grind)
    | exact superpose eq257 eq1375
    | (have j0 := eq1375 X0 X1
       grind)
    | exact resolve eq1375 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1375
  have eq1415 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1385 X0 X1
       have i₂ := eq257 X0 X0
       grind)
    | exact superpose eq257 eq1385
    | (have j0 := eq1385 X0 X1
       grind)
    | exact resolve eq1385 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq1385
  have eq7908 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq1415 X0 (τ X1)
       grind)
    | exact superpose eq1415 eq35
    | (have j1 := eq1415 X0 (τ X1)
       grind)
    | exact resolve eq35 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq7911 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq137
       have i₂ := eq1415 X0 sF0
       grind)
    | exact superpose eq1415 eq137
    | (have j1 := eq1415 X0 (M.op x y)
       grind)
    | exact resolve eq137 eq1415
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7925 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1415 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1415
  have eq7931 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op X0 X0) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq7911
    | (have j0 := eq7911 X0
       grind)
    | exact resolve eq7911 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7911
  have eq7934 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq7908 X0 X1
       have j1 := eq1111 X0 (σ (τ X1)) X1
       grind)
    | (have r₁ := eq7908 X0 X1
       have r₂ := eq1111 X0 (k X1 (σ (τ X1))) x
       grind)
    | (have r₁ := eq7908 X0 X1
       have r₂ := eq1111 X0 (σ (τ X1)) x
       grind)
    | exact resolve eq7908 eq1111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7908
  have eq7999 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq7931 X0
       have j1 := eq1111 X0 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq7931 X0
       have r₂ := eq1111 X0 (σ (M.op x y)) x
       grind)
    | (have r₁ := eq7931 X0
       have r₂ := eq1111 X0 (k (σ (M.op x y)) (σ (M.op x y))) x
       grind)
    | exact resolve eq7931 eq1111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1111 eq7931
  have eq8002 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7934 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq7934
    | exact resolve eq7934 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7934
  have eq8172 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq7999 eq160
    | exact resolve eq160 eq7999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq8708 : ∀ X1 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (k X1 X1) := by
    intro X1
    first
    | (have i₁ := eq8002 x X1
       have i₂ := eq7999 x
       grind)
    | exact superpose eq7999 eq8002
    | exact resolve eq8002 eq7999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8887 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq137
       have i₂ := eq8002 X0 sF0
       grind)
    | exact superpose eq8002 eq137
    | exact resolve eq137 eq8002
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq8002
  have eq9351 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq8708 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq8708
    | exact resolve eq8708 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32240 : ∀ X0 X1 : G, (σ X1) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7925 X0 X1
       have i₂ := eq9351 X1
       grind)
    | exact superpose eq9351 eq7925
    | (have j0 := eq7925 X0 X1
       grind)
    | exact resolve eq7925 eq9351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7925 eq9351
  have eq32573 : ∀ X0 X1 : G, (k (σ (M.op x y)) (σ (M.op x y))) ≠ X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq32240 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq32240
    | (have r₁ := eq32240 X0 (τ (k (σ (M.op x y)) (σ (M.op x y))))
       have r₂ := eq15 (k (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq32240 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32240
  have eq32660 : ∀ X0 X1 X2 : G, (k X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq32573 X0 X1
       have i₂ := eq8708 sF1
       grind)
    | exact superpose eq8708 eq32573
    | (have j0 := eq32573 X1 X2
       grind)
    | (have r₁ := eq32573 (k X1 X1) X1
       have r₂ := eq8708 X1
       grind)
    | (have r₁ := eq32573 (k (σ (M.op x y)) (σ (M.op x y))) X1
       have r₂ := eq8708 (σ (M.op x y))
       grind)
    | exact resolve eq32573 eq8708
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8708
  have eq32661 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq7999 eq32573
    | (have j0 := eq32573 X1 X2
       grind)
    | (have r₁ := eq32573 (M.op X0 X0) X1
       have r₂ := eq7999 X0
       grind)
    | exact resolve eq32573 eq7999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7999 eq32573
  have eq41221 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq32661 x y x
       grind)
    | (have r₁ := eq93
       have r₂ := eq32661 x y x
       grind)
    | (have r₁ := eq93
       have r₂ := eq32661 y y x
       grind)
    | exact resolve eq93 eq32661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq41235 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq41221 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq41221
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41221
  have eq41236 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq32661 x (σ y) (σ x)
       grind)
    | (have r₁ := eq41235
       have r₂ := eq32661 (σ x) (σ y) x
       grind)
    | (have r₁ := eq41235
       have r₂ := eq32661 (σ y) (σ y) x
       grind)
    | (have r₁ := eq41235
       have r₂ := eq32661 x y x
       grind)
    | exact resolve eq41235 eq32661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32661 eq41235
  have eq41245 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq41236
    | exact resolve eq41236 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41236
  have eq41247 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq41245
       have r₂ := eq28
       grind)
    | exact resolve eq41245 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41245
  have eq41289 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq41247 eq8172
    | exact resolve eq8172 eq41247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8172 eq41247
  have eq41322 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq41289
    | exact resolve eq41289 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq41289
  have eq41344 : y = (M.op x x) := by
    first
    | (have j1 := eq32660 x y x
       grind)
    | (have r₁ := eq41322
       have r₂ := eq32660 (M.op x y) y x
       grind)
    | exact resolve eq41322 eq32660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32660 eq41322
  have eq41350 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq41344
       have i₂ := eq248 x X0
       grind)
    | (have i₁ := eq41344
       have i₂ := eq248 X0 x
       grind)
    | exact superpose eq248 eq41344
    | exact resolve eq41344 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248
  have eq41391 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq8887 x
       have i₂ := eq41344
       grind)
    | exact superpose eq41344 eq8887
    | exact resolve eq8887 eq41344
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8887 eq41344
  have eq41421 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq41391
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq41391
    | exact resolve eq41391 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41391
  have eq41616 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq14 (M.op x x) x x
       have i₂ := eq41350 (M.op x x)
       grind)
    | exact superpose eq41350 eq14
    | exact resolve eq14 eq41350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41657 : y = (M.op x y) := by
    first
    | (have i₁ := eq52 sF0
       have i₂ := eq41350 sF0
       grind)
    | exact superpose eq41350 eq52
    | exact resolve eq52 eq41350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq41696 : y = (M.op x y) := by
    first
    | (have i₁ := eq41657
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq41657
    | exact resolve eq41657 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq41657
  have eq41898 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq41696 eq21
    | exact resolve eq21 eq41696
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq41696
  have eq42038 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq41898
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq41898
    | exact resolve eq41898 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq41898
  have eq42072 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq42038 eq27
    | exact resolve eq27 eq42038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq42268 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq42038 eq41421
    | exact resolve eq41421 eq42038
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41421 eq42038
  have eq42338 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq42268 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | exact resolve eq11 eq42268
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42268
  have eq42339 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq42338
  have eq42342 : y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq42339
       have i₂ := eq41350 sF1
       grind)
    | exact superpose eq41350 eq42339
    | exact resolve eq42339 eq41350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41350 eq42339
  have eq47810 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq42342 eq42072
    | exact resolve eq42072 eq42342
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42072
  have eq47811 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq47810
       have i₂ := eq41616 sF2
       grind)
    | exact superpose eq41616 eq47810
    | exact resolve eq47810 eq41616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41616 eq47810
  have eq47818 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq47811 eq28
    | exact resolve eq28 eq47811
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq47811
  have eq47819 : False := by grind
  exact eq47819

/-- `Equation3273`: `x ◇ x = y ◇ (x ◇ (y ◇ z))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,Y) else if m(X,X) = Y then X else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxx_y_pyy_x_pxy_Equation3273 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) Law3273 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3273.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a a = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X1 (M.op X0 (M.op X1 X2))) := by
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
  clear eq23
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
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
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
  have eq45 : (σ (k x y)) = (k (σ x) (σ y)) := by
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
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (M.op x (M.op X0 (M.op x y))) := by
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
  have eq54 : ∀ X0 X1 X2 X3 : G, (M.op X3 X3) = (M.op X1 (M.op X3 (M.op X0 (M.op X1 (M.op X0 X2))))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 X1 X1
       have i₂ := eq14 X1 X0 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X1 (M.op X0 X0))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 X1 X2 (M.op X0 (M.op X2 x))
       have i₂ := eq14 X0 X2 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X0 (M.op X1 x)
       have i₂ := eq14 X0 X1 x
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 (M.op X0 X2))) ≠ X1 ∨ (M.op X0 (M.op X1 (M.op X0 X2))) = (k X3 X1) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq77 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq84 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq45
       have i₂ := eq11 x y
       grind)
    | exact superpose eq11 eq45
    | (have j1 := eq11 x y
       grind)
    | exact resolve eq45 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq92 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq84
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq84
    | exact resolve eq84 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq93 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) ∨ y = (M.op y y) := by
    first
    | exact superpose eq21 eq92
    | exact resolve eq92 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq117 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X1 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    grind
  have eq120 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (M.op X0 X0)) ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq117 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq137 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq160 : (k (M.op x y) (M.op x y)) = (τ (k (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq137 eq16
    | exact resolve eq16 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq248 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq56 x X0
       have i₂ := eq56 x X1
       grind)
    | exact superpose eq56 eq56
    | exact resolve eq56 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 X1 X1
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq14
    | exact resolve eq14 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq392 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq16
    | exact resolve eq16 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq424 : ∀ X0 X1 X2 : G, (M.op X1 X1) = (M.op X2 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq55 X1 X1 X2
       have i₂ := eq56 X1 X0
       grind)
    | exact superpose eq56 eq55
    | exact resolve eq55 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq710 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (k X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq424 X0 X1 X2
       grind)
    | (have i₁ := eq13 X0 (M.op X0 X0)
       have i₂ := eq424 X0 X1 (M.op X0 X0)
       grind)
    | exact superpose eq424 eq13
    | (have r₁ := eq13 X0 (M.op X2 (M.op X0 X0))
       have r₂ := eq424 X0 (M.op X2 (M.op X0 X0)) X2
       grind)
    | (have r₁ := eq13 X0 (M.op X1 X1)
       have r₂ := eq424 X1 X1 (M.op X1 X1)
       grind)
    | exact resolve eq13 eq424
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq729 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k X2 (M.op X1 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq710 X0 X1 X2
       grind)
    | (have r₁ := eq710 X0 X1 X2
       have r₂ := eq248 X0 X1
       grind)
    | (have r₁ := eq710 X1 X0 X2
       have r₂ := eq248 X0 X1
       grind)
    | exact resolve eq710 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq710
  have eq1019 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (k X0 (M.op X0 X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq120 X0 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq1053 : ∀ X0 X1 X4 : G, (M.op X0 (M.op X0 X0)) ≠ X1 ∨ (M.op X0 (M.op X0 X0)) = (k X4 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq67 x X1 (M.op X0 (M.op X1 (M.op X0 x))) x
       have i₂ := eq54 X0 X1 x x
       grind)
    | exact superpose eq54 eq67
    | exact resolve eq67 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54 eq67
  have eq1085 : ∀ X0 X1 X4 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 (M.op X0 X0)) = (k X4 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq1053 X0 X1 X4
       have i₂ := eq257 X0 X0
       grind)
    | exact superpose eq257 eq1053
    | (have j0 := eq1053 X0 X1 X4
       grind)
    | (have r₁ := eq1053 X0 (M.op X0 X0) X4
       have r₂ := eq257 X0 X0
       grind)
    | exact resolve eq1053 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1053
  have eq1095 : ∀ X0 X1 X4 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X4 X1) := by
    intro X0 X1 X4
    first
    | (have i₁ := eq1085 X0 X1 X4
       have i₂ := eq257 X0 X0
       grind)
    | exact superpose eq257 eq1085
    | (have j0 := eq1085 X0 X1 X4
       grind)
    | (have r₁ := eq1085 X1 (M.op X1 (M.op X0 X0)) X4
       have r₂ := eq257 X0 X1
       grind)
    | (have r₁ := eq1085 (M.op X0 X0) (M.op (M.op X0 X0) (M.op X0 X0)) X4
       have r₂ := eq257 X0 (M.op X0 X0)
       grind)
    | exact resolve eq1085 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1085
  have eq1406 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq77 X0 X0
       have i₂ := eq56 X0 (σ X0)
       grind)
    | exact superpose eq56 eq77
    | exact resolve eq77 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq77
  have eq1471 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X0)) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1406 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1406
  have eq1481 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (σ X1) = (M.op X0 (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1471 X0 X1
       have i₂ := eq257 X0 X0
       grind)
    | exact superpose eq257 eq1471
    | (have j0 := eq1471 X0 X1
       grind)
    | exact resolve eq1471 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1471
  have eq1511 : ∀ X0 X1 : G, (M.op X0 X0) = (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq1481 X0 X1
       have i₂ := eq257 X0 X0
       grind)
    | exact superpose eq257 eq1481
    | (have j0 := eq1481 X0 X1
       grind)
    | exact resolve eq1481 eq257
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257 eq1481
  have eq1815 : ∀ X0 X1 X2 : G, (k X1 (τ (M.op X2 X2))) = (τ (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq392 X1 (M.op X2 X2)
       have i₂ := eq729 X0 X2 (σ X1)
       grind)
    | exact superpose eq729 eq392
    | exact resolve eq392 eq729
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392 eq729
  have eq8305 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) ∨ (M.op X0 X0) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq35 X1 (τ X1)
       have i₂ := eq1511 X0 (τ X1)
       grind)
    | exact superpose eq1511 eq35
    | (have j1 := eq1511 X0 (τ X1)
       grind)
    | exact resolve eq35 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq8307 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) ∨ (M.op X0 X0) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq75
       have i₂ := eq1511 X0 y
       grind)
    | exact superpose eq1511 eq75
    | (have j1 := eq1511 X0 y
       grind)
    | exact resolve eq75 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq8308 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = (σ (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq137
       have i₂ := eq1511 X0 sF0
       grind)
    | exact superpose eq1511 eq137
    | (have j1 := eq1511 X0 (M.op x y)
       grind)
    | exact resolve eq137 eq1511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8322 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X1)) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq1511 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1511
  have eq8328 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op x y)) ∨ (M.op X0 X0) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq21 eq8308
    | (have j0 := eq8308 X0
       grind)
    | exact resolve eq8308 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8308
  have eq8329 : ∀ X0 : G, (M.op X0 X0) = (σ y) ∨ (M.op X0 X0) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq8307 X0
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq8307
    | (have j0 := eq8307 X0
       grind)
    | exact resolve eq8307 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8307
  have eq8331 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq8305 X0 X1
       have j1 := eq1095 X0 (σ (τ X1)) X1
       grind)
    | (have r₁ := eq8305 X0 X1
       have r₂ := eq1095 X0 (k X1 (σ (τ X1))) x
       grind)
    | (have r₁ := eq8305 X0 X1
       have r₂ := eq1095 X0 (σ (τ X1)) x
       grind)
    | exact resolve eq8305 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8305
  have eq8399 : ∀ X0 : G, (M.op X0 X0) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    intro X0
    first
    | (have j0 := eq8328 X0
       have j1 := eq1095 X0 (σ (M.op x y)) (σ (M.op x y))
       grind)
    | (have r₁ := eq8328 X0
       have r₂ := eq1095 X0 (σ (M.op x y)) x
       grind)
    | (have r₁ := eq8328 X0
       have r₂ := eq1095 X0 (k (σ (M.op x y)) (σ (M.op x y))) x
       grind)
    | exact resolve eq8328 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8328
  have eq8400 : ∀ X0 : G, (M.op X0 X0) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have j0 := eq8329 X0
       have j1 := eq1095 X0 (σ y) (σ y)
       grind)
    | (have r₁ := eq8329 X0
       have r₂ := eq1095 X0 (σ y) x
       grind)
    | (have r₁ := eq8329 X0
       have r₂ := eq1095 X0 (k (σ y) (σ y)) x
       grind)
    | exact resolve eq8329 eq1095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1095 eq8329
  have eq8402 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8331 X0 X1
       have i₂ := eq15 X1
       grind)
    | exact superpose eq15 eq8331
    | exact resolve eq8331 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8331
  have eq8577 : ∀ X0 : G, (k (M.op x y) (M.op x y)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq8399 eq160
    | exact resolve eq160 eq8399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq160
  have eq8639 : (k (σ y) (σ y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq8400 x
       have i₂ := eq8399 x
       grind)
    | exact superpose eq8399 eq8400
    | exact resolve eq8400 eq8399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq8694 : ∀ X0 : G, (k (σ y) (σ y)) ≠ X0 ∨ (k X0 (k (σ y) (σ y))) = X0 := by
    intro X0
    first
    | (have i₁ := eq1019 X0
       have i₂ := eq8400 X0
       grind)
    | exact superpose eq8400 eq1019
    | (have r₁ := eq1019 (k (σ y) (σ y))
       have r₂ := eq8400 (k (σ y) (σ y))
       grind)
    | exact resolve eq1019 eq8400
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1019 eq8400
  have eq9134 : ∀ X1 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (k X1 X1) := by
    intro X1
    first
    | (have i₁ := eq8402 x X1
       have i₂ := eq8399 x
       grind)
    | exact superpose eq8399 eq8402
    | exact resolve eq8402 eq8399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9137 : ∀ X0 X2 : G, (k X0 X0) = (k X2 X2) := by
    intro X0 X2
    first
    | (have i₁ := eq8402 x X2
       have i₂ := eq8402 x X0
       grind)
    | exact superpose eq8402 eq8402
    | exact resolve eq8402 eq8402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9164 : ∀ X0 X1 : G, (M.op X1 X1) = (σ (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq8402 X1 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq8402
    | exact resolve eq8402 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9249 : ∀ X0 X1 : G, (k X0 X0) = (M.op X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (M.op X1 x) X1 x
       have i₂ := eq8402 (M.op X1 x) X1
       grind)
    | exact superpose eq8402 eq14
    | exact resolve eq14 eq8402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq9802 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq9134 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq9134
    | exact resolve eq9134 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9134
  have eq10320 : ∀ X0 X1 X3 : G, (τ (M.op X3 X3)) = (k X1 (τ (σ (k X0 X0)))) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq1815 X3 X1 x
       have i₂ := eq9164 X0 x
       grind)
    | exact superpose eq9164 eq1815
    | exact resolve eq1815 eq9164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1815 eq9164
  have eq10423 : ∀ X0 X1 X3 : G, (τ (M.op X3 X3)) = (k X1 (k X0 X0)) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq10320 X0 X1 X3
       have i₂ := eq16 (k X0 X0)
       grind)
    | exact superpose eq16 eq10320
    | exact resolve eq10320 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10320
  have eq10454 : ∀ X0 X1 : G, (k (M.op x y) (M.op x y)) = (k X1 (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq10423 X0 X1 x
       have i₂ := eq8577 x
       grind)
    | exact superpose eq8577 eq10423
    | exact resolve eq10423 eq8577
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10423
  have eq35584 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) ≠ X0 ∨ (k X0 (k (σ y) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq8639 eq8694
    | (have j0 := eq8694 X0
       grind)
    | (have r₁ := eq8694 (k (σ (M.op x y)) (σ (M.op x y)))
       have r₂ := eq8639
       grind)
    | exact resolve eq8694 eq8639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8639 eq8694
  have eq35585 : ∀ X0 : G, (k (σ (M.op x y)) (σ (M.op x y))) ≠ X0 ∨ (k (M.op x y) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq35584 x
       have i₂ := eq10454 sF3 x
       grind)
    | exact superpose eq10454 eq35584
    | (have j0 := eq35584 X0
       grind)
    | exact resolve eq35584 eq10454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10454 eq35584
  have eq35587 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k (M.op x y) (M.op x y)) = X1 := by
    intro X0 X1
    first
    | exact superpose eq8399 eq35585
    | (have j0 := eq35585 X1
       grind)
    | (have r₁ := eq35585 (M.op X0 X0)
       have r₂ := eq8399 X0
       grind)
    | exact resolve eq35585 eq8399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35585
  have eq36897 : ∀ X0 X1 : G, (σ X1) ≠ (k (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op X0 X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8322 X0 X1
       have i₂ := eq9802 X1
       grind)
    | exact superpose eq9802 eq8322
    | (have j0 := eq8322 X0 X1
       grind)
    | exact resolve eq8322 eq9802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8322 eq9802
  have eq36905 : ∀ X0 X1 : G, (k (σ (M.op x y)) (σ (M.op x y))) ≠ X0 ∨ (M.op X1 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq36897 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq36897
    | (have r₁ := eq36897 X0 (τ (k (σ (M.op x y)) (σ (M.op x y))))
       have r₂ := eq15 (k (σ (M.op x y)) (σ (M.op x y)))
       grind)
    | exact resolve eq36897 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36897
  have eq36999 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X2 X2) = X1 := by
    intro X0 X1 X2
    first
    | exact superpose eq8399 eq36905
    | (have j0 := eq36905 X1 X2
       grind)
    | (have r₁ := eq36905 (M.op X0 X0) X1
       have r₂ := eq8399 X0
       grind)
    | exact resolve eq36905 eq8399
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8399 eq36905
  have eq46078 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq36999 x y x
       grind)
    | (have r₁ := eq93
       have r₂ := eq36999 x y x
       grind)
    | (have r₁ := eq93
       have r₂ := eq36999 y y x
       grind)
    | exact resolve eq93 eq36999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq46089 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq46078 eq11
    | (have j0 := eq11 (σ x) (σ y)
       grind)
    | exact resolve eq11 eq46078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46078
  have eq46096 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have j1 := eq36999 x (σ y) (σ x)
       grind)
    | (have r₁ := eq46089
       have r₂ := eq36999 (σ x) (σ y) x
       grind)
    | (have r₁ := eq46089
       have r₂ := eq36999 (σ y) (σ y) x
       grind)
    | (have r₁ := eq46089
       have r₂ := eq36999 x y x
       grind)
    | exact resolve eq46089 eq36999
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36999 eq46089
  have eq46107 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq27 eq46096
    | exact resolve eq46096 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46096
  have eq46109 : (σ y) = (M.op (σ x) (σ x)) ∨ y = (M.op x x) := by
    first
    | (have r₁ := eq46107
       have r₂ := eq28
       grind)
    | exact resolve eq46107 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46107
  have eq46153 : (τ (σ y)) = (k (M.op x y) (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq46109 eq8577
    | exact resolve eq8577 eq46109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8577 eq46109
  have eq46196 : y = (k (M.op x y) (M.op x y)) ∨ y = (M.op x x) := by
    first
    | exact superpose eq30 eq46153
    | exact resolve eq46153 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq46153
  have eq46220 : y = (k (M.op x y) (M.op x y)) := by
    first
    | (have j1 := eq35587 x y
       grind)
    | (have r₁ := eq46196
       have r₂ := eq35587 x y
       grind)
    | exact resolve eq46196 eq35587
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35587 eq46196
  have eq46226 : ∀ X0 : G, y = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq46220
       have i₂ := eq9137 sF0 x
       grind)
    | (have i₁ := eq46220
       have i₂ := eq9137 X0 sF0
       grind)
    | exact superpose eq9137 eq46220
    | exact resolve eq46220 eq9137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9137
  have eq46228 : ∀ X0 : G, (M.op X0 X0) = y := by
    intro X0
    first
    | (have i₁ := eq46220
       have i₂ := eq8402 X0 sF0
       grind)
    | exact superpose eq8402 eq46220
    | exact resolve eq46220 eq8402
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8402
  have eq46250 : ∀ X0 : G, y = (M.op X0 y) := by
    intro X0
    first
    | exact superpose eq46220 eq9249
    | exact resolve eq9249 eq46220
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9249 eq46220
  have eq46511 : (σ y) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq137
       have i₂ := eq46226 sF0
       grind)
    | exact superpose eq46226 eq137
    | exact resolve eq137 eq46226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq46559 : y = (σ y) := by
    first
    | (have i₁ := eq46511
       have i₂ := eq46226 sF1
       grind)
    | exact superpose eq46226 eq46511
    | exact resolve eq46511 eq46226
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46226 eq46511
  have eq46674 : y = (σ y) := by
    first
    | (have i₁ := eq46559
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq46559
    | exact resolve eq46559 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46559
  have eq46796 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq46674 eq27
    | exact resolve eq27 eq46674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq47172 : y = (M.op x y) := by
    first
    | (have i₁ := eq52 sF0
       have i₂ := eq46228 sF0
       grind)
    | exact superpose eq46228 eq52
    | exact resolve eq52 eq46228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq46228
  have eq47213 : y = (M.op x y) := by
    first
    | (have i₁ := eq47172
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq47172
    | exact resolve eq47172 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq47172
  have eq47485 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq47213 eq21
    | exact resolve eq21 eq47213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq47213
  have eq47631 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq47485
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq47485
    | exact resolve eq47485 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq47485
  have eq47686 : y = (σ (M.op x y)) := by
    first
    | exact superpose eq46674 eq47631
    | exact resolve eq47631 eq46674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46674 eq47631
  have eq52655 : y = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq46796
       have i₂ := eq46250 sF2
       grind)
    | exact superpose eq46250 eq46796
    | exact resolve eq46796 eq46250
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46250 eq46796
  have eq52664 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq52655 eq28
    | exact resolve eq28 eq52655
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq52655
  have eq52665 : False := by grind
  exact eq52665
