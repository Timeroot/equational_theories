import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(X,Y) else if m(X,Y) = Y then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pxy_y_pxy_y_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq61 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq61 (σ X0)
       grind)
    | exact superpose eq61 eq15
    | exact resolve eq15 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq64 X0
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq64
    | exact resolve eq64 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq64
  have eq86 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq352 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 (M.op X1 X1)
       have r₂ := eq12 (M.op X1 X1) X1
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
  have eq353 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq352 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq352
    | (have j0 := eq352 (σ X0) (σ X1)
       grind)
    | exact resolve eq352 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq377 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq17 X0 X1
       have i₂ := eq352 (τ X0) X1
       grind)
    | exact superpose eq352 eq17
    | (have j1 := eq352 (τ X0) X1
       grind)
    | exact resolve eq17 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq385 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq377 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq377
    | exact resolve eq377 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq416 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq385 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq385
    | (have j0 := eq385 X0 X1
       grind)
    | exact resolve eq385 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq385
  have eq662 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
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
  have eq672 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq353 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq353
  have eq784 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq662
       have i₂ := eq352 x y
       grind)
    | exact superpose eq352 eq662
    | (have j1 := eq352 (σ x) (σ y)
       grind)
    | exact resolve eq662 eq352
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq352 eq662
  have eq787 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq784
  have eq789 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq787
       grind)
    | exact superpose eq787 eq16
    | exact resolve eq16 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq791 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq787
       grind)
    | exact superpose eq787 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq787
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq787
       grind)
    | exact resolve eq13 eq787
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq793 : (σ y) = (k (σ x) (σ y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq791
  have eq795 : (σ y) = (σ (k x y)) ∨ (M.op (σ y) (σ x)) = (M.op (σ y) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq793
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq793
    | exact resolve eq793 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq793
  have eq799 : (M.op (σ y) (σ x)) = (σ (M.op y y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq795
       have i₂ := eq75 y
       grind)
    | exact superpose eq75 eq795
    | exact resolve eq795 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq795
  have eq9445 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq86 y (σ x)
       have i₂ := eq799
       grind)
    | exact superpose eq799 eq86
    | (have j0 := eq86 y (σ x)
       grind)
    | (have r₁ := eq86 y (σ x)
       have r₂ := eq799
       grind)
    | exact resolve eq86 eq799
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq799
  have eq9459 : (M.op (σ x) (σ y)) = (k (σ x) (σ y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by grind
  clear eq9445
  have eq9472 : (M.op (σ x) (σ y)) = (σ (k x y)) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq9459
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq9459
    | exact resolve eq9459 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9459
  have eq12724 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) ∨ (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq787
       have i₂ := eq9472
       grind)
    | exact superpose eq9472 eq787
    | exact resolve eq787 eq9472
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq787 eq9472
  have eq12769 : (σ y) = (σ (k x y)) ∨ y = (M.op x y) := by grind
  clear eq12724
  have eq12811 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq416 x y
       have i₂ := eq12769
       grind)
    | exact superpose eq12769 eq416
    | (have j0 := eq416 x y
       grind)
    | exact resolve eq416 eq12769
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq416 eq12769
  have eq12876 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq12811
  have eq12903 : y = (M.op x y) := by
    first
    | (have r₁ := eq12876
       have r₂ := eq789
       grind)
    | exact resolve eq12876 eq789
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq789 eq12876
  have eq12908 : y ≠ y ∨ y = (k x y) ∨ (M.op y y) = (M.op y x) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq12903
       grind)
    | exact superpose eq12903 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq12903
       grind)
    | exact resolve eq13 eq12903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12909 : (M.op y y) = (M.op y x) ∨ y = (k x y) := by grind
  clear eq12908
  have eq12914 : ∀ X0 : G, (M.op y x) ≠ (M.op y X0) ∨ (k X0 y) = (M.op X0 y) ∨ y = (k x y) := by
    intro X0
    first
    | (have i₁ := eq12 X0 y
       have i₂ := eq12909
       grind)
    | exact superpose eq12909 eq12
    | (have j0 := eq12 X0 y
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq12909
       grind)
    | exact resolve eq12 eq12909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12909
  have eq12937 : (M.op x y) = (k x y) ∨ y = (k x y) := by
    first
    | (have j0 := eq12914 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12914
  have eq12940 : y = (k x y) ∨ y = (k x y) := by
    first
    | (have i₁ := eq12937
       have i₂ := eq12903
       grind)
    | exact superpose eq12903 eq12937
    | exact resolve eq12937 eq12903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12937
  have eq12941 : y = (k x y) := by grind
  clear eq12940
  have eq12957 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq672 x y
       have i₂ := eq12941
       grind)
    | exact superpose eq12941 eq672
    | (have j0 := eq672 x y
       grind)
    | exact resolve eq672 eq12941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq672 eq12941
  have eq13000 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12957
  have eq13018 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13000
       grind)
    | exact superpose eq13000 eq16
    | exact resolve eq16 eq13000
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13000
  have eq13028 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq13018
       have i₂ := eq12903
       grind)
    | exact superpose eq12903 eq13018
    | exact resolve eq13018 eq12903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12903 eq13018
  have eq13029 : False := by grind
  exact eq13029

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyx_pyx_pyy_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
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
  have eq19 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq34 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq34 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq46 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq48 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X1 X1
       grind)
    | (have r₁ := eq44 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq53 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq45 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq57 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq47 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq47 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq64 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq53 X0 X1
       have j1 := eq48 X1 X0
       grind)
    | (have r₁ := eq53 X1 X1
       have r₂ := eq48 X0 X1
       grind)
    | exact resolve eq53 eq48
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48 eq53
  have eq65 : ∀ X0 X1 : G, (M.op X1 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq57 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq57
    | (have j0 := eq57 X0 X1
       grind)
    | exact resolve eq57 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq57
  have eq162 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq64 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq258 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X3) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X0) X3 X4
       have i₂ := eq19 X0 X1 X2
       grind)
    | (have i₁ := eq9 (M.op X2 X2) X1 X2
       have i₂ := eq19 X2 X2 X2
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2630 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X3) (M.op X3 X4)) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq258 X1 X1 X2 X3 X4
       have i₂ := eq65 X0 X1
       grind)
    | (have i₁ := eq258 X0 X1 X2 X3 X4
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq258
    | (have j1 := eq65 X0 X1
       grind)
    | exact resolve eq258 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq2753 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X3) (M.op X3 X4)) ≠ (M.op X0 X5) ∨ (M.op X0 X5) = (k X5 X0) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq162 X5 X0
       have i₂ := eq258 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq258 eq162
    | (have j0 := eq162 X5 X0
       grind)
    | exact resolve eq162 eq258
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq162 eq258
  have eq2937 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2630 X0 X1 x x x
       have j1 := eq2753 X0 X1 x x x X1
       grind)
    | (have r₁ := eq2630 X0 X1 x x x
       have r₂ := eq2753 X0 X1 x x x X1
       grind)
    | exact resolve eq2630 eq2753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2630 eq2753
  have eq82467 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2937 (σ X0) (σ X1)
       grind)
    | exact superpose eq2937 eq15
    | exact resolve eq15 eq2937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq82489 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq82467 X0 X1
       have i₂ := eq2937 X0 X1
       grind)
    | exact superpose eq2937 eq82467
    | exact resolve eq82467 eq2937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2937 eq82467
  have eq82516 : False := by grind
  exact eq82516

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,X) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxx_pyy_pxy_pyx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a a = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
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
  have eq24 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq9 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq46 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq45 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq45 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq45 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq59 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 (M.op X1 X1) X1
       have r₂ := eq12 (M.op X1 X1) (M.op X1 X1)
       grind)
    | (have r₁ := eq14 X0 (M.op X0 X0)
       have r₂ := eq12 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq59 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq59
    | (have j0 := eq59 (σ X0) (σ X1)
       grind)
    | exact resolve eq59 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq46 (τ X0)
       grind)
    | exact superpose eq46 eq18
    | exact resolve eq18 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq86 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq85
    | exact resolve eq85 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq94 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq86 X0
       have i₂ := eq46 X0
       grind)
    | exact superpose eq46 eq86
    | exact resolve eq86 eq46
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46 eq86
  have eq98 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq94 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq94
    | exact resolve eq94 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq106 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X0 X1) X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq24 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq24
    | exact resolve eq24 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq182 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq70 x y
       grind)
    | exact superpose eq70 eq16
    | (have j1 := eq70 x y
       grind)
    | exact resolve eq16 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq715 : (M.op (σ x) (σ x)) = (σ (M.op y y)) ∨ (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq182
       have i₂ := eq98 y
       grind)
    | exact superpose eq98 eq182
    | exact resolve eq182 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq716 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq715
       have i₂ := eq98 x
       grind)
    | exact superpose eq98 eq715
    | exact resolve eq715 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq753 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq716
       have i₂ := eq59 x y
       grind)
    | exact superpose eq59 eq716
    | (have j1 := eq59 y x
       grind)
    | exact resolve eq716 eq59
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59 eq716
  have eq754 : (σ (M.op y y)) = (σ (M.op x x)) ∨ (M.op y y) = (M.op x x) := by grind
  clear eq753
  have eq9920 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq754
       grind)
    | exact superpose eq754 eq10
    | exact resolve eq10 eq754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq754
  have eq9959 : (M.op y y) = (M.op x x) ∨ (M.op y y) = (M.op x x) := by
    first
    | (have i₁ := eq9920
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq9920
    | exact resolve eq9920 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9920
  have eq9960 : (M.op y y) = (M.op x x) := by grind
  clear eq9959
  have eq10171 : ∀ X0 : G, y = (M.op (M.op (M.op x x) (M.op x x)) (M.op (M.op x x) X0)) := by
    intro X0
    first
    | (have i₁ := eq106 y y x
       have i₂ := eq9960
       grind)
    | exact superpose eq9960 eq106
    | exact resolve eq106 eq9960
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq9960
  have eq10212 : x = y := by
    first
    | (have i₁ := eq10171 x
       have i₂ := eq9 x (M.op x x) x
       grind)
    | exact superpose eq9 eq10171
    | exact resolve eq10171 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10171
  have eq10237 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq10212
       grind)
    | exact superpose eq10212 eq16
    | exact resolve eq16 eq10212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10212
  have eq10238 : False := by grind
  exact eq10238

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxy_pyx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
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
  have eq91 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 (σ X0) (σ X1)
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 (σ X1) (σ X0)
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq525 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq12 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq526 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq91 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq91 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq91 X0 X1
       grind)
    | exact resolve eq13 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq537 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq526 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq543 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq537 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq537 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq537 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq537 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq537
  have eq544 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq525 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq525 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq525 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq525
  have eq553 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq543 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq543
    | (have j0 := eq543 X0 X1
       grind)
    | exact resolve eq543 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq543
  have eq554 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq553 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq553
  have eq555 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq544 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq544
    | (have j0 := eq544 X0 X1
       grind)
    | exact resolve eq544 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544
  have eq556 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq555 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq555
  have eq561 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq556 X0 X1
       have j1 := eq554 X0 X1
       grind)
    | (have r₁ := eq556 X0 X1
       have r₂ := eq554 X0 X1
       grind)
    | exact resolve eq556 eq554
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq554 eq556
  have eq562 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq561 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq561
    | exact resolve eq561 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq573 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq561 x y
       grind)
    | exact superpose eq561 eq16
    | exact resolve eq16 eq561
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq561
  have eq684 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq562 X0 (τ X1)
       grind)
    | exact superpose eq562 eq18
    | exact resolve eq18 eq562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq562
  have eq707 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq684 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq684
    | exact resolve eq684 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq684
  have eq718 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq707 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq707
    | exact resolve eq707 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq707
  have eq745 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq573
       have i₂ := eq718 x y
       grind)
    | exact superpose eq718 eq573
    | exact resolve eq573 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq573 eq718
  have eq746 : False := by grind
  exact eq746

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if m(X,Y) = m(Y,X) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pyx_pyy_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    grind
  have eq18 : ∀ X0 : G, (τ (σ X0)) = (τ (σ X0)) := by
    intro X0
    first
    | (have j0 := eq17 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17
  have eq19 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq10 X0
       grind)
    | exact resolve eq10 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    grind
  have eq21 : ∀ X0 : G, (σ (τ X0)) = (σ (τ X0)) := by
    intro X0
    first
    | (have j0 := eq20 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq22 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0
       grind)
    | exact resolve eq11 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : (M.op x y) = (M.op x y) := by grind
  have eq24 : (M.op x y) = (M.op x y) := by grind
  clear eq23
  have eq25 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  have eq26 : (σ (M.op x y)) = (σ (M.op x y)) := by grind
  clear eq25
  have eq27 : (σ x) = (σ x) := by grind
  have eq28 : (σ x) = (σ x) := by grind
  clear eq27
  have eq29 : (σ y) = (σ y) := by grind
  have eq30 : (σ y) = (σ y) := by grind
  clear eq29
  have eq31 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  have eq32 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ y)) := by grind
  clear eq31
  have eq33 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq34 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq19 eq18
    | (have j1 := eq19 X0
       grind)
    | exact resolve eq18 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq19
  have eq35 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    first
    | exact superpose eq22 eq21
    | (have j1 := eq22 X0
       grind)
    | exact resolve eq21 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq22
  have eq36 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq26 eq34
    | (have j0 := eq34 (M.op x y)
       grind)
    | exact resolve eq34 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : x = (τ (σ x)) := by
    first
    | (have i₁ := eq34 x
       have i₂ := eq28
       grind)
    | exact superpose eq28 eq34
    | (have j0 := eq34 x
       grind)
    | exact resolve eq34 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq40 : y = (τ (σ y)) := by
    first
    | (have i₁ := eq34 y
       have i₂ := eq30
       grind)
    | exact superpose eq30 eq34
    | (have j0 := eq34 y
       grind)
    | exact resolve eq34 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq41 : (M.op x y) = (M.op (τ (σ x)) y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq38
       grind)
    | exact superpose eq38 eq24
    | exact resolve eq24 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq38
  have eq42 : (M.op x y) = (M.op (τ (σ x)) (τ (σ y))) := by
    first
    | (have i₁ := eq41
       have i₂ := eq40
       grind)
    | exact superpose eq40 eq41
    | exact resolve eq41 eq40
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq41
  have eq46 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq34 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq34
    | exact resolve eq34 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq47 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq46 (τ X0) X1
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq46
    | exact resolve eq46 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 X1 : G, (k X1 (τ X0)) = (τ (k (σ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq46 X1 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq46
    | exact resolve eq46 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (σ (M.op x y)))) := by
    intro X0
    first
    | exact superpose eq26 eq46
    | (have j0 := eq46 X0 (M.op x y)
       grind)
    | exact resolve eq46 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq46
  have eq62 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq63 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op X0 X0) (M.op (M.op X0 X0) X1) X2
       have i₂ := eq9 X0 (M.op X0 X0) X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (τ (σ x))) (M.op x y)) = X0 := by
    intro X0
    first
    | exact superpose eq42 eq9
    | exact resolve eq9 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq32 eq9
    | (have j0 := eq9 X0 (σ x) (σ y)
       grind)
    | exact resolve eq9 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq81 : (M.op x y) ≠ (τ (σ y)) ∨ (M.op x y) = (k (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq42 eq12
    | exact resolve eq12 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq83 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq32 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq105 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq105 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq105 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq105 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq116 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq47 X1 (τ X0)
       have i₂ := eq35 X0
       grind)
    | exact superpose eq35 eq47
    | exact resolve eq47 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq134 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (τ (σ y)) := by
    first
    | exact superpose eq42 eq14
    | exact resolve eq14 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq136 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq32 eq14
    | (have j0 := eq14 (σ y) (σ x)
       grind)
    | exact resolve eq14 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq155 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq136
       have r₂ := eq83
       grind)
    | exact resolve eq136 eq83
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83 eq136
  have eq157 : (M.op x y) = (k (τ (σ y)) (τ (σ x))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | (have r₁ := eq134
       have r₂ := eq81
       grind)
    | exact resolve eq134 eq81
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81 eq134
  have eq198 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (τ (σ x))) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq65 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq65
    | exact resolve eq65 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq212 : ∀ X0 : G, (M.op (M.op X0 (τ (σ x))) (M.op x y)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq198 X0
       have i₂ := eq106 (M.op X0 X0)
       grind)
    | exact superpose eq106 eq198
    | exact resolve eq198 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198
  have eq218 : ∀ X0 : G, (M.op (M.op X0 (τ (σ x))) (M.op x y)) = (k (k X0 X0) (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq212 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq212
    | exact resolve eq212 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq228 : ∀ X0 : G, (M.op (M.op (k X0 X0) (τ (σ x))) (M.op x y)) = X0 := by
    intro X0
    first
    | (have i₁ := eq65 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq65
    | exact resolve eq65 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq229 : ∀ X0 X1 X2 : G, (M.op (M.op (k X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X0 X1 X2
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq9
    | exact resolve eq9 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq230 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) X0) (k X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq9 X1 X0 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq9
    | exact resolve eq9 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq235 : ∀ X0 X1 : G, (M.op (M.op (k X1 X1) X0) (k X0 X0)) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq230 X0 X1
       have i₂ := eq106 X1
       grind)
    | exact superpose eq106 eq230
    | exact resolve eq230 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq236 : ∀ X0 : G, (k (k (k X0 X0) (k X0 X0)) (k (k X0 X0) (k X0 X0))) = X0 := by
    intro X0
    first
    | exact superpose eq218 eq228
    | exact resolve eq228 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq271 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq67 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq67
    | exact resolve eq67 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq285 : ∀ X0 : G, (k (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq271 X0
       have i₂ := eq106 (M.op X0 X0)
       grind)
    | exact superpose eq106 eq271
    | exact resolve eq271 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq291 : ∀ X0 : G, (k (k X0 X0) (k X0 X0)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq285 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq285
    | exact resolve eq285 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq285
  have eq321 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (k (σ y) (σ x))) = X0 ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | exact superpose eq155 eq67
    | exact resolve eq67 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq322 : (σ (M.op x y)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq155 eq33
    | exact resolve eq33 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq323 : ∀ X0 : G, (M.op (M.op (k X0 X0) (σ x)) (k (σ y) (σ x))) = X0 ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq321 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq321
    | exact resolve eq321 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq321
  have eq357 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op X0 (M.op (M.op (k X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X0 X1 X2
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq63
    | exact resolve eq63 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq366 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k (M.op (M.op (M.op X0 X0) X1) X2) X0) ∨ (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) = (M.op (M.op (M.op (M.op X0 X0) X1) X2) X0) ∨ (M.op (M.op (M.op X0 X0) X1) X2) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq63 X0 X1 X2
       have i₂ := eq14 (M.op (M.op (M.op X0 X0) X1) X2) X0
       grind)
    | exact superpose eq14 eq63
    | (have j1 := eq14 (M.op (M.op (M.op X0 X0) X1) X2) X0
       grind)
    | exact resolve eq63 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq368 : ∀ X0 X1 X2 : G, (M.op X0 X0) ≠ (M.op (M.op (M.op X0 X0) X1) X2) ∨ (M.op X0 X0) = (k (M.op (M.op (M.op X0 X0) X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op (M.op (M.op X0 X0) X1) X2) X0
       have i₂ := eq63 X0 X1 X2
       grind)
    | exact superpose eq63 eq12
    | exact resolve eq12 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq370 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) X2) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X0 (M.op (M.op (M.op (M.op X0 X0) (M.op X0 X0)) X1) X2) X3
       have i₂ := eq63 (M.op X0 X0) X1 X2
       grind)
    | exact superpose eq63 eq9
    | exact resolve eq9 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq371 : ∀ X0 X1 X2 X3 : G, (M.op (k (M.op X0 X0) (M.op X0 X0)) (M.op (M.op (M.op (k (M.op X0 X0) (M.op X0 X0)) X1) X2) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq370 X0 X1 X2 X3
       have i₂ := eq106 (M.op X0 X0)
       grind)
    | exact superpose eq106 eq370
    | exact resolve eq370 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq370
  have eq372 : ∀ X0 X1 X2 : G, (k X0 X0) ≠ (M.op (M.op (k X0 X0) X1) X2) ∨ (M.op X0 X0) = (k (M.op (M.op (M.op X0 X0) X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq368 X0 X1 X2
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq368
    | (have j0 := eq368 X0 X1 X2
       grind)
    | exact resolve eq368 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq368
  have eq374 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (k (M.op (M.op (M.op X0 X0) X1) X2) X0) ∨ (M.op (M.op (M.op X0 X0) X1) X2) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq366 X0 X1 X2
       have j1 := eq13 (M.op (M.op (M.op X0 X0) X1) X2) X0
       grind)
    | (have r₁ := eq366 X1 X1 X2
       have r₂ := eq13 (M.op (M.op (M.op X1 X1) X1) X2) X1
       grind)
    | (have r₁ := eq366 X0 X1 X2
       have r₂ := eq13 X0 (M.op (M.op (M.op X0 X0) X1) X2)
       grind)
    | exact resolve eq366 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq366
  have eq380 : ∀ X0 X1 X2 X3 : G, (M.op (k (k X0 X0) (k X0 X0)) (M.op (M.op (M.op (k (k X0 X0) (k X0 X0)) X1) X2) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq371 X0 X1 X2 X3
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq371
    | exact resolve eq371 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq371
  have eq381 : ∀ X0 X1 X2 : G, (k X0 X0) ≠ (M.op (M.op (k X0 X0) X1) X2) ∨ (k X0 X0) = (k (M.op (M.op (k X0 X0) X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq372 X0 X1 X2
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq372
    | (have j0 := eq372 X0 X1 X2
       grind)
    | exact resolve eq372 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq372
  have eq383 : ∀ X0 X1 X2 : G, (k X0 X0) = (k (M.op (M.op (k X0 X0) X1) X2) X0) ∨ (M.op (M.op (M.op X0 X0) X1) X2) = (M.op X0 (M.op (M.op (M.op X0 X0) X1) X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq374 X0 X1 X2
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq374
    | (have j0 := eq374 X0 X1 X2
       grind)
    | exact resolve eq374 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq374
  have eq388 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op X0 X0) X1) X2) ∨ (k X0 X0) = (k (M.op (M.op (k X0 X0) X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq383 X0 X1 X2
       have i₂ := eq63 X0 X1 X2
       grind)
    | exact superpose eq63 eq383
    | (have j0 := eq383 X0 X1 X2
       grind)
    | exact resolve eq383 eq63
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq63 eq383
  have eq392 : ∀ X0 X1 X2 : G, (k X0 X0) = (M.op (M.op (k X0 X0) X1) X2) ∨ (k X0 X0) = (k (M.op (M.op (k X0 X0) X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq388 X0 X1 X2
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq388
    | (have j0 := eq388 X0 X1 X2
       grind)
    | exact resolve eq388 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq388
  have eq393 : ∀ X0 X1 X2 : G, (k X0 X0) = (k (M.op (M.op (k X0 X0) X1) X2) X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq392 X0 X1 X2
       have j1 := eq381 X0 X1 X2
       grind)
    | (have r₁ := eq392 X0 X1 X2
       have r₂ := eq381 X0 X1 X2
       grind)
    | exact resolve eq392 eq381
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq381 eq392
  have eq428 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ x)))) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | exact superpose eq157 eq15
    | exact resolve eq15 eq157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq157
  have eq429 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ x)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq428
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq428
    | exact resolve eq428 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq428
  have eq430 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) := by
    first
    | (have i₁ := eq429
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq429
    | exact resolve eq429 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq431 : (M.op x y) = (M.op (τ (σ y)) (τ (σ x))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq430
    | exact resolve eq430 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq433 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (M.op (M.op X1 X1) X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 X1 (M.op (M.op X0 X0) (M.op X0 X0)) X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq435 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) (M.op (M.op X0 X0) (M.op X0 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq64 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq64
    | exact resolve eq64 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq439 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (k (M.op X0 X0) (M.op X0 X0))) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq64 X0 X1 (M.op X0 X0)
       have i₂ := eq106 (M.op X0 X0)
       grind)
    | exact superpose eq106 eq64
    | exact resolve eq64 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq465 : ∀ X0 X1 : G, (M.op (M.op (M.op X1 X1) (k (k X0 X0) (k X0 X0))) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq439 X0 X1
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq439
    | exact resolve eq439 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq439
  have eq467 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) (k (M.op X0 X0) (M.op X0 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq435 X0 X1 X2
       have i₂ := eq106 (M.op X0 X0)
       grind)
    | exact superpose eq106 eq435
    | exact resolve eq435 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq435
  have eq469 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (M.op (k X1 X1) X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq433 X0 X1 X2
       have i₂ := eq106 X1
       grind)
    | exact superpose eq106 eq433
    | exact resolve eq433 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433
  have eq481 : ∀ X0 X1 : G, (M.op (M.op (k X1 X1) (k (k X0 X0) (k X0 X0))) X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq465 X0 X1
       have i₂ := eq106 X1
       grind)
    | exact superpose eq106 eq465
    | exact resolve eq465 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq465
  have eq483 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op X0 X2)) (k (k X0 X0) (k X0 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq467 X0 X1 X2
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq467
    | exact resolve eq467 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467
  have eq484 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (M.op (k X1 X1) X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq469 X0 X1 X2
       have i₂ := eq106 (M.op X0 X0)
       grind)
    | exact superpose eq106 eq469
    | exact resolve eq469 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq469
  have eq493 : ∀ X0 X1 X2 : G, (M.op (M.op (k X1 X1) (M.op X0 X2)) (k (k X0 X0) (k X0 X0))) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq483 X0 X1 X2
       have i₂ := eq106 X1
       grind)
    | exact superpose eq106 eq483
    | exact resolve eq483 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq483
  have eq494 : ∀ X0 X1 X2 : G, (k (k X0 X0) (k X0 X0)) = (M.op (M.op X0 (M.op (k X1 X1) X2)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq484 X0 X1 X2
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq484
    | exact resolve eq484 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq484
  have eq512 : (M.op x y) ≠ (M.op (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (k (τ (σ x)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq431 eq13
    | (have j0 := eq13 (τ (σ x)) (τ (σ y))
       grind)
    | exact resolve eq13 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq513 : (M.op x y) ≠ (τ (σ x)) ∨ (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq431 eq12
    | exact resolve eq12 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq516 : (M.op x y) = (τ (σ x)) ∨ (k (τ (σ x)) (τ (σ y))) = (M.op (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq512
       have r₂ := eq42
       grind)
    | exact resolve eq512 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq520 : (k (τ (σ x)) (τ (σ y))) = (k (τ (σ y)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq516
       have i₂ := eq106 (τ sF5)
       grind)
    | exact superpose eq106 eq516
    | exact resolve eq516 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq516
  have eq526 : (M.op (M.op x y) (M.op x y)) = (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq431 eq218
    | exact resolve eq218 eq431
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431
  have eq532 : ∀ X0 : G, (τ (σ x)) = (M.op (k (k (τ (σ x)) (τ (σ x))) (k (τ (σ x)) (τ (σ x)))) (M.op (M.op x y) X0)) := by
    intro X0
    first
    | exact superpose eq218 eq9
    | exact resolve eq9 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq549 : (k (M.op x y) (M.op x y)) = (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq526
       have i₂ := eq106 sF2
       grind)
    | exact superpose eq106 eq526
    | exact resolve eq526 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq526
  have eq562 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))) (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)))) = (M.op X0 (M.op X1 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) X1 X3
       have i₂ := eq64 X1 X0 X2
       grind)
    | exact superpose eq64 eq62
    | exact resolve eq62 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64
  have eq563 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1))) = (M.op X0 (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq62 (M.op (M.op X0 X0) X1) (M.op X1 X2) X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq62
    | exact resolve eq62 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq569 : ∀ X0 : G, (M.op (M.op (τ (σ x)) (τ (σ x))) (M.op (τ (σ x)) (τ (σ x)))) = (M.op (M.op x y) (M.op (τ (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq42 eq62
    | exact resolve eq62 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq572 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq32 eq62
    | (have j0 := eq62 (σ x) (σ y) X0
       grind)
    | exact resolve eq62 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq574 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X1 X1)) = (M.op (M.op X1 X0) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq62 X1 X0 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq62
    | exact resolve eq62 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq601 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (k (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq106 (M.op X0 X0)
       have i₂ := eq62 X0 X1 X2
       grind)
    | (have i₁ := eq106 (M.op X2 X2)
       have i₂ := eq62 X2 X2 X2
       grind)
    | exact superpose eq62 eq106
    | exact resolve eq106 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq613 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (M.op (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X1 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq62 X0 X1 X2
       grind)
    | (have i₁ := eq12 (M.op X1 X2) (M.op X0 X1)
       have i₂ := eq62 X0 X1 X2
       grind)
    | exact superpose eq62 eq12
    | (have r₁ := eq12 (M.op (M.op X0 X0) (M.op X0 X0)) (M.op X0 (M.op X0 X0))
       have r₂ := eq62 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq12 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq616 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X1 X2) (M.op X0 X1)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X1 X2) (M.op X0 X1)) ∨ (M.op X1 X2) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op X0 X0) (M.op X0 X0)
       have i₂ := eq62 X0 X1 X2
       grind)
    | (have i₁ := eq14 (M.op X1 X2) (M.op X0 X1)
       have i₂ := eq62 X0 X1 X2
       grind)
    | exact superpose eq62 eq14
    | exact resolve eq14 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq619 : ∀ X0 X1 X2 : G, (k (M.op X0 X0) (M.op X0 X0)) = (k (M.op X1 X2) (M.op X0 X1)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X1 X2) (M.op X0 X1)) ∨ (M.op X1 X2) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq616 X0 X1 X2
       have i₂ := eq106 (M.op X0 X0)
       grind)
    | exact superpose eq106 eq616
    | (have j0 := eq616 X0 X1 X2
       grind)
    | exact resolve eq616 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq622 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (k (M.op X0 X0) (M.op X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X1 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq613 X0 X1 X2
       have i₂ := eq106 (M.op X0 X0)
       grind)
    | exact superpose eq106 eq613
    | (have j0 := eq613 X0 X1 X2
       grind)
    | exact resolve eq613 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq629 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X1 X2)) = (k (k X0 X0) (k X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq601 X0 X1 X2
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq601
    | exact resolve eq601 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq601
  have eq651 : ∀ X0 X1 : G, (M.op (M.op X1 X0) (k X0 X0)) = (k (M.op X1 X1) (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq574 X0 X1
       have i₂ := eq106 (M.op X1 X1)
       grind)
    | exact superpose eq106 eq574
    | exact resolve eq574 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq574
  have eq653 : ∀ X0 : G, (k (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq572 X0
       have i₂ := eq106 (M.op sF4 sF4)
       grind)
    | exact superpose eq106 eq572
    | exact resolve eq572 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq572
  have eq656 : ∀ X0 : G, (k (M.op (τ (σ x)) (τ (σ x))) (M.op (τ (σ x)) (τ (σ x)))) = (M.op (M.op x y) (M.op (τ (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq569 X0
       have i₂ := eq106 (M.op (τ sF4) (τ sF4))
       grind)
    | exact superpose eq106 eq569
    | exact resolve eq569 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq569
  have eq662 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (k (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq563 X0 X1 X2 X3
       have i₂ := eq106 (M.op (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1))
       grind)
    | exact superpose eq106 eq563
    | exact resolve eq563 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq563
  have eq663 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X3)) = (k (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))) (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq562 X0 X1 X2 X3
       have i₂ := eq106 (M.op (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)))
       grind)
    | exact superpose eq106 eq562
    | exact resolve eq562 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq562
  have eq670 : ∀ X0 X1 X2 : G, (k (k X0 X0) (k X0 X0)) = (k (M.op X1 X2) (M.op X0 X1)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X1 X2) (M.op X0 X1)) ∨ (M.op X1 X2) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq619 X0 X1 X2
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq619
    | (have j0 := eq619 X0 X1 X2
       grind)
    | exact resolve eq619 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq673 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (k (k X0 X0) (k X0 X0)) ∨ (M.op (M.op X0 X0) (M.op X0 X0)) = (k (M.op X1 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq622 X0 X1 X2
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq622
    | (have j0 := eq622 X0 X1 X2
       grind)
    | (have r₁ := eq622 X0 (M.op X0 X0) (M.op X0 X0)
       have r₂ := eq106 (M.op X0 X0)
       grind)
    | exact resolve eq622 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq622
  have eq699 : ∀ X0 X1 : G, (k (k X1 X1) (k X1 X1)) = (M.op (M.op X1 X0) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq651 X0 X0
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq651
    | exact resolve eq651 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq701 : ∀ X0 : G, (k (k (σ x) (σ x)) (k (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq653 X0
       have i₂ := eq106 sF4
       grind)
    | exact superpose eq106 eq653
    | exact resolve eq653 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq653
  have eq704 : ∀ X0 : G, (k (k (τ (σ x)) (τ (σ x))) (k (τ (σ x)) (τ (σ x)))) = (M.op (M.op x y) (M.op (τ (σ y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq656 X0
       have i₂ := eq106 (τ sF4)
       grind)
    | exact superpose eq106 eq656
    | exact resolve eq656 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq656
  have eq710 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op (M.op X1 X2) X3)) = (k (k (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1)) (k (M.op (M.op X0 X0) X1) (M.op (M.op X0 X0) X1))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq662 X0 X1 X2 X3
       have i₂ := eq106 (M.op (M.op X0 X0) X1)
       grind)
    | exact superpose eq106 eq662
    | exact resolve eq662 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq662
  have eq711 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X3)) = (k (k (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))) (k (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)) (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq663 X0 X1 X2 X3
       have i₂ := eq106 (M.op (M.op X0 X0) (M.op (M.op X1 X1) X2))
       grind)
    | exact superpose eq106 eq663
    | exact resolve eq663 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663
  have eq715 : ∀ X0 X1 X2 : G, (k (k X0 X0) (k X0 X0)) = (M.op (M.op X1 X2) (M.op X0 X1)) ∨ (k (k X0 X0) (k X0 X0)) = (k (M.op X1 X2) (M.op X0 X1)) ∨ (M.op X1 X2) = (M.op (M.op X0 X0) (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq670 X0 X1 X2
       have i₂ := eq629 X0 X0 X0
       grind)
    | exact superpose eq629 eq670
    | (have j0 := eq670 X0 X1 X2
       grind)
    | exact resolve eq670 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq670
  have eq718 : ∀ X0 X1 X2 : G, (M.op X1 X2) ≠ (k (k X0 X0) (k X0 X0)) ∨ (k (k X0 X0) (k X0 X0)) = (k (M.op X1 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq673 X0 X1 X2
       have i₂ := eq629 X0 X0 X0
       grind)
    | exact superpose eq629 eq673
    | (have j0 := eq673 X0 X1 X2
       grind)
    | (have r₁ := eq673 X0 (M.op X0 X1) (M.op X1 X2)
       have r₂ := eq629 X0 X1 X2
       grind)
    | exact resolve eq673 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673
  have eq735 : ∀ X0 X1 X2 X3 : G, (k (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1)) (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1))) = (M.op X0 (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq710 X0 X1 X2 X3
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq710
    | exact resolve eq710 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq710
  have eq736 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X3)) = (k (k (M.op (M.op X0 X0) (M.op (k X1 X1) X2)) (M.op (M.op X0 X0) (M.op (k X1 X1) X2))) (k (M.op (M.op X0 X0) (M.op (k X1 X1) X2)) (M.op (M.op X0 X0) (M.op (k X1 X1) X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq711 X0 X0 X2 X3
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq711
    | exact resolve eq711 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711
  have eq738 : ∀ X0 X1 X2 : G, (M.op X1 X2) = (k (k X0 X0) (k X0 X0)) ∨ (k (k X0 X0) (k X0 X0)) = (M.op (M.op X1 X2) (M.op X0 X1)) ∨ (k (k X0 X0) (k X0 X0)) = (k (M.op X1 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq715 X0 X1 X2
       have i₂ := eq629 X0 X0 X0
       grind)
    | exact superpose eq629 eq715
    | (have j0 := eq715 X0 X1 X2
       grind)
    | exact resolve eq715 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq715
  have eq743 : ∀ X0 X1 X2 X3 : G, (M.op X0 (M.op X1 X3)) = (k (k (M.op (k X0 X0) (M.op (k X1 X1) X2)) (M.op (k X0 X0) (M.op (k X1 X1) X2))) (k (M.op (k X0 X0) (M.op (k X1 X1) X2)) (M.op (k X0 X0) (M.op (k X1 X1) X2)))) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq736 X0 X1 X2 X3
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq736
    | exact resolve eq736 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq736
  have eq744 : ∀ X0 X1 X2 : G, (k (k X0 X0) (k X0 X0)) = (k (M.op X1 X2) (M.op X0 X1)) ∨ (k (k X0 X0) (k X0 X0)) = (M.op (M.op X1 X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq738 X0 X1 X2
       have j1 := eq718 X0 X1 X2
       grind)
    | (have r₁ := eq738 X0 X1 X2
       have r₂ := eq718 X0 X1 X2
       grind)
    | (have r₁ := eq738 X0 X1 X2
       have r₂ := eq718 X0 (M.op X1 X2) (M.op X0 X1)
       grind)
    | exact resolve eq738 eq718
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq718 eq738
  have eq1161 : (k (k (τ (σ x)) (τ (σ x))) (k (τ (σ x)) (τ (σ x)))) = (M.op (M.op x y) (k (τ (σ y)) (τ (σ y)))) := by
    first
    | (have i₁ := eq704 (τ sF5)
       have i₂ := eq106 (τ sF5)
       grind)
    | exact superpose eq106 eq704
    | exact resolve eq704 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq704
  have eq1192 : ∀ X0 X1 : G, (M.op (M.op (k (k (τ (σ x)) (τ (σ x))) (k (τ (σ x)) (τ (σ x)))) (k (k (τ (σ x)) (τ (σ x))) (k (τ (σ x)) (τ (σ x))))) (M.op (k (k (τ (σ x)) (τ (σ x))) (k (τ (σ x)) (τ (σ x)))) (k (k (τ (σ x)) (τ (σ x))) (k (τ (σ x)) (τ (σ x)))))) = (M.op (τ (σ x)) (M.op (M.op (M.op x y) X0) X1)) := by
    intro X0 X1
    first
    | exact superpose eq532 eq62
    | exact resolve eq62 eq532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq532
  have eq1197 : ∀ X0 X1 : G, (M.op (τ (σ x)) (M.op (M.op (M.op x y) X0) X1)) = (k (k (k (k (τ (σ x)) (τ (σ x))) (k (τ (σ x)) (τ (σ x)))) (k (k (τ (σ x)) (τ (σ x))) (k (τ (σ x)) (τ (σ x))))) (k (k (k (τ (σ x)) (τ (σ x))) (k (τ (σ x)) (τ (σ x)))) (k (k (τ (σ x)) (τ (σ x))) (k (τ (σ x)) (τ (σ x)))))) := by
    intro X0 X1
    first
    | (have i₁ := eq1192 X0 X1
       have i₂ := eq629 (k (k (τ sF4) (τ sF4)) (k (τ sF4) (τ sF4))) (k (k (τ sF4) (τ sF4)) (k (τ sF4) (τ sF4))) (k (k (τ sF4) (τ sF4)) (k (τ sF4) (τ sF4)))
       grind)
    | exact superpose eq629 eq1192
    | exact resolve eq1192 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1192
  have eq1202 : ∀ X0 X1 : G, (k (τ (σ x)) (τ (σ x))) = (M.op (τ (σ x)) (M.op (M.op (M.op x y) X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1197 X0 X1
       have i₂ := eq236 (k (τ sF4) (τ sF4))
       grind)
    | exact superpose eq236 eq1197
    | exact resolve eq1197 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1197
  have eq1263 : (k (τ (σ x)) (τ (σ x))) = (M.op (τ (σ x)) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) := by
    first
    | exact superpose eq218 eq1202
    | exact resolve eq1202 eq218
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq218 eq1202
  have eq1356 : (k (τ (σ x)) (τ (σ x))) ≠ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (k (τ (σ x)) (τ (σ x))) = (k (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (τ (σ x))) := by
    first
    | exact superpose eq1263 eq12
    | exact resolve eq12 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1357 : (k (τ (σ x)) (τ (σ x))) ≠ (M.op (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ x))) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (M.op (τ (σ x)) (τ (σ x))) = (k (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (τ (σ x))) := by
    first
    | exact superpose eq1263 eq13
    | (have j0 := eq13 (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (τ (σ x))
       grind)
    | exact resolve eq13 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1359 : (k (τ (σ x)) (τ (σ x))) = (k (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ x))) = (M.op (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ x))) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq1263 eq14
    | exact resolve eq14 eq1263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1263
  have eq1372 : (k (τ (σ x)) (τ (σ x))) = (k (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ x))) ≠ (M.op (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ x))) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq1357
       have i₂ := eq106 (τ sF4)
       grind)
    | exact superpose eq106 eq1357
    | exact resolve eq1357 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1357
  have eq1376 : (k (τ (σ x)) (τ (σ x))) = (k (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (τ (σ x))) ∨ (k (τ (σ x)) (τ (σ x))) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) := by
    first
    | (have r₁ := eq1372
       have r₂ := eq1359
       grind)
    | exact resolve eq1372 eq1359
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1359 eq1372
  have eq1379 : (k (τ (σ x)) (τ (σ x))) = (k (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (τ (σ x))) := by
    first
    | (have r₁ := eq1376
       have r₂ := eq1356
       grind)
    | exact resolve eq1376 eq1356
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1356 eq1376
  have eq1528 : (k (σ (τ (σ x))) (σ (τ (σ x)))) = (σ (k (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (τ (σ x)))) := by
    first
    | exact superpose eq1379 eq15
    | exact resolve eq15 eq1379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1529 : (k (σ (τ (σ x))) (σ (τ (σ x)))) = (k (σ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) (σ (τ (σ x)))) := by
    first
    | (have i₁ := eq1528
       have i₂ := eq15 (k (k sF2 sF2) (k sF2 sF2)) (τ sF4)
       grind)
    | exact superpose eq15 eq1528
    | exact resolve eq1528 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1528
  have eq1531 : (k (σ x) (σ x)) = (k (σ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) (σ x)) := by
    first
    | (have i₁ := eq1529
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq1529
    | exact resolve eq1529 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1529
  have eq1533 : (k (σ x) (σ x)) = (k (k (σ (k (M.op x y) (M.op x y))) (σ (k (M.op x y) (M.op x y)))) (σ x)) := by
    first
    | (have i₁ := eq1531
       have i₂ := eq15 (k sF2 sF2) (k sF2 sF2)
       grind)
    | exact superpose eq15 eq1531
    | exact resolve eq1531 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1531
  have eq1535 : (k (σ x) (σ x)) = (k (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) (σ x)) := by
    first
    | (have i₁ := eq1533
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq1533
    | exact resolve eq1533 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1533
  have eq1536 : (k (σ x) (σ x)) = (k (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) (σ x)) := by
    first
    | exact superpose eq26 eq1535
    | exact resolve eq1535 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1535
  have eq3409 : (k (τ (σ y)) (τ (σ y))) = (k (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq549 eq236
    | exact resolve eq236 eq549
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq549
  have eq3430 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3409
       have i₂ := eq236 sF2
       grind)
    | exact superpose eq236 eq3409
    | exact resolve eq3409 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3409
  have eq3514 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3430 eq520
    | exact resolve eq520 eq3430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq520
  have eq3538 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3430 eq15
    | exact resolve eq15 eq3430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3540 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (M.op x y) = (τ (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  clear eq3514
  have eq3542 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3538
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq3538
    | exact resolve eq3538 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3538
  have eq3545 : (M.op x y) = (k (τ (σ x)) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq3540
       have r₂ := eq513
       grind)
    | exact resolve eq3540 eq513
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq513 eq3540
  have eq3547 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq3542
    | exact resolve eq3542 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3542
  have eq3560 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3547 eq322
    | (have r₁ := eq322
       have r₂ := eq3547
       grind)
    | exact resolve eq322 eq3547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3562 : (k (σ x) (σ x)) = (k (k (k (k (σ y) (σ y)) (k (σ y) (σ y))) (k (k (σ y) (σ y)) (k (σ y) (σ y)))) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3547 eq1536
    | exact resolve eq1536 eq3547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1536
  have eq3565 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by grind
  have eq3568 : (k (σ y) (σ x)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3562
       have i₂ := eq236 sF5
       grind)
    | exact superpose eq236 eq3562
    | exact resolve eq3562 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3562
  have eq3570 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq3560
       have r₂ := eq322
       grind)
    | exact resolve eq3560 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3560
  have eq3594 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3545 eq15
    | exact resolve eq15 eq3545
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3545
  have eq3595 : (σ (M.op x y)) = (k (σ (τ (σ x))) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3594
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq3594
    | exact resolve eq3594 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3594
  have eq3597 : (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq3595
       have i₂ := eq35 sF4
       grind)
    | exact superpose eq35 eq3595
    | exact resolve eq3595 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3595
  have eq3598 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq3597
    | exact resolve eq3597 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3597
  have eq3599 : (k (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3547 eq3598
    | exact resolve eq3598 eq3547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3547
  have eq3610 : (k (σ y) (σ x)) ≠ (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq3598 eq322
    | (have r₁ := eq322
       have r₂ := eq3598
       grind)
    | exact resolve eq322 eq3598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3613 : (k (σ y) (σ x)) ≠ (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  have eq3614 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq3610
  have eq3625 : (k (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq3599
       have r₂ := eq3565
       grind)
    | exact resolve eq3599 eq3565
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3565 eq3599
  have eq4211 : (k (σ y) (σ x)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3625 eq3570
    | exact resolve eq3570 eq3625
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3570 eq3625
  have eq4243 : (k (σ y) (σ x)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq4211
       have r₂ := eq322
       grind)
    | exact resolve eq4211 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4211
  have eq4625 : (k (σ x) (σ x)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3568 eq4243
    | exact resolve eq4243 eq3568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3568 eq4243
  have eq4628 : (k (σ x) (σ x)) ≠ (k (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq4625
       have r₂ := eq322
       grind)
    | exact resolve eq4625 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4625
  have eq8145 : ∀ X0 X1 : G, (M.op x y) = (k (M.op (M.op (M.op x y) X0) X1) (τ (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq3430 eq393
    | exact resolve eq393 eq3430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393
  have eq8682 : (k (k (σ x) (σ x)) (k (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq701 (M.op (M.op (k sF5 sF5) x) x)
       have i₂ := eq357 sF5 x x
       grind)
    | exact superpose eq357 eq701
    | exact resolve eq701 eq357
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq357
  have eq11407 : ∀ X0 X1 : G, (σ (M.op x y)) = (k (σ (M.op (M.op (M.op x y) X0) X1)) (σ (τ (σ y)))) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq8145 eq15
    | exact resolve eq15 eq8145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8145
  have eq11412 : ∀ X0 X1 : G, (σ (M.op x y)) = (k (σ (M.op (M.op (M.op x y) X0) X1)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq11407 X0 X1
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq11407
    | exact resolve eq11407 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11407
  have eq11417 : ∀ X0 X1 : G, (σ (M.op x y)) = (k (σ (M.op (M.op (M.op x y) X0) X1)) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq26 eq11412
    | (have j0 := eq11412 X0 X1
       grind)
    | exact resolve eq11412 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11412
  have eq12302 : ∀ X0 X1 X2 : G, (k (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1)) (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1))) = (M.op X0 (k (M.op X1 X2) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq699 (M.op X1 X2) (M.op (k X0 X0) X1)
       have i₂ := eq229 X0 X1 X2
       grind)
    | exact superpose eq229 eq699
    | exact resolve eq699 eq229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq12305 : ∀ X0 X1 : G, (k (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1)) (k (M.op (k X0 X0) X1) (M.op (k X0 X0) X1))) = (M.op X0 (k (k X1 X1) (k X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq699 (k X1 X1) (M.op (k X0 X0) X1)
       have i₂ := eq235 X1 X0
       grind)
    | exact superpose eq235 eq699
    | exact resolve eq699 eq235
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12491 : ∀ X0 X1 X2 : G, (M.op X0 (k (k X1 X1) (k X1 X1))) = (M.op X0 (k (M.op X1 X2) (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12302 X0 X1 X2
       have i₂ := eq12305 X0 X1
       grind)
    | exact superpose eq12305 eq12302
    | exact resolve eq12302 eq12305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12302
  have eq12916 : (τ (σ y)) = (M.op (M.op (M.op x y) (σ x)) (k (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq3430 eq323
    | exact resolve eq323 eq3430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq323 eq3430
  have eq13008 : (τ (σ y)) = (M.op (M.op (M.op x y) (σ x)) (k (σ y) (σ x))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq12916
       have r₂ := eq322
       grind)
    | exact resolve eq12916 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12916
  have eq13030 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | exact superpose eq13008 eq11417
    | exact resolve eq11417 eq13008
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11417 eq13008
  have eq13089 : (σ (M.op x y)) = (k (σ (τ (σ y))) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) := by
    first
    | (have r₁ := eq13030
       have r₂ := eq322
       grind)
    | exact resolve eq13030 eq322
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq322 eq13030
  have eq13097 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq13089
       have i₂ := eq35 sF5
       grind)
    | exact superpose eq35 eq13089
    | exact resolve eq13089 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13089
  have eq14425 : ∀ X0 X1 X2 : G, (k (k (M.op (k X0 X0) (M.op X1 X2)) (M.op (k X0 X0) (M.op X1 X2))) (k (M.op (k X0 X0) (M.op X1 X2)) (M.op (k X0 X0) (M.op X1 X2)))) = (M.op X0 (k (k (k X1 X1) (k X1 X1)) (k (k X1 X1) (k X1 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq699 (k (k X1 X1) (k X1 X1)) (M.op (k X0 X0) (M.op X1 X2))
       have i₂ := eq493 X1 X0 X2
       grind)
    | exact superpose eq493 eq699
    | exact resolve eq699 eq493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493 eq699
  have eq14440 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k (k (M.op (k X0 X0) (M.op X1 X2)) (M.op (k X0 X0) (M.op X1 X2))) (k (M.op (k X0 X0) (M.op X1 X2)) (M.op (k X0 X0) (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14425 X0 X1 X2
       have i₂ := eq236 X1
       grind)
    | exact superpose eq236 eq14425
    | exact resolve eq14425 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14425
  have eq14529 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X0 (k (k (M.op X1 X2) (M.op X1 X2)) (k (M.op X1 X2) (M.op X1 X2)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14440 X0 X1 X2
       have i₂ := eq12305 X0 (M.op X1 X2)
       grind)
    | exact superpose eq12305 eq14440
    | exact resolve eq14440 eq12305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14440
  have eq15055 : ∀ X0 X1 : G, (M.op (k (k X0 X0) (k X0 X0)) X1) = (k (k (M.op X0 (k X1 X1)) (M.op X0 (k X1 X1))) (k (M.op X0 (k X1 X1)) (M.op X0 (k X1 X1)))) := by
    intro X0 X1
    first
    | (have i₁ := eq494 (M.op X0 (k X1 X1)) X1 x
       have i₂ := eq629 X0 (k X1 X1) x
       grind)
    | exact superpose eq629 eq494
    | exact resolve eq494 eq629
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494 eq629
  have eq25434 : ∀ X0 X1 X2 : G, (k (k (M.op (k X0 X0) (k (k X1 X1) (k X1 X1))) (M.op (k X0 X0) (k (k X1 X1) (k X1 X1)))) (k (M.op (k X0 X0) (k (k X1 X1) (k X1 X1))) (M.op (k X0 X0) (k (k X1 X1) (k X1 X1))))) = (k (M.op X1 X2) X0) ∨ (M.op (M.op X1 X2) X0) = (k (k (M.op (k X0 X0) (k (k X1 X1) (k X1 X1))) (M.op (k X0 X0) (k (k X1 X1) (k X1 X1)))) (k (M.op (k X0 X0) (k (k X1 X1) (k X1 X1))) (M.op (k X0 X0) (k (k X1 X1) (k X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq744 (M.op (k X1 X1) (k (k X0 X0) (k X0 X0))) X0 X2
       have i₂ := eq481 X0 X1
       grind)
    | exact superpose eq481 eq744
    | exact resolve eq744 eq481
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq481 eq744
  have eq25698 : ∀ X0 X1 X2 : G, (M.op X0 (k (k (k (k X1 X1) (k X1 X1)) (k (k X1 X1) (k X1 X1))) (k (k (k X1 X1) (k X1 X1)) (k (k X1 X1) (k X1 X1))))) = (k (M.op X1 X2) X0) ∨ (M.op (M.op X1 X2) X0) = (k (k (M.op (k X0 X0) (k (k X1 X1) (k X1 X1))) (M.op (k X0 X0) (k (k X1 X1) (k X1 X1)))) (k (M.op (k X0 X0) (k (k X1 X1) (k X1 X1))) (M.op (k X0 X0) (k (k X1 X1) (k X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25434 X0 X1 X2
       have i₂ := eq12305 X0 (k (k X1 X1) (k X1 X1))
       grind)
    | exact superpose eq12305 eq25434
    | (have j0 := eq25434 X0 X1 X2
       grind)
    | exact resolve eq25434 eq12305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25434
  have eq25796 : ∀ X0 X1 X2 : G, (M.op X0 (k X1 X1)) = (k (M.op X1 X2) X0) ∨ (M.op (M.op X1 X2) X0) = (k (k (M.op (k X0 X0) (k (k X1 X1) (k X1 X1))) (M.op (k X0 X0) (k (k X1 X1) (k X1 X1)))) (k (M.op (k X0 X0) (k (k X1 X1) (k X1 X1))) (M.op (k X0 X0) (k (k X1 X1) (k X1 X1))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25698 X0 X1 X2
       have i₂ := eq236 (k X1 X1)
       grind)
    | exact superpose eq236 eq25698
    | (have j0 := eq25698 X0 X1 X2
       grind)
    | exact resolve eq25698 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25698
  have eq25859 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) X0) = (M.op X0 (k (k (k (k X1 X1) (k X1 X1)) (k (k X1 X1) (k X1 X1))) (k (k (k X1 X1) (k X1 X1)) (k (k X1 X1) (k X1 X1))))) ∨ (M.op X0 (k X1 X1)) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25796 X0 X1 X2
       have i₂ := eq12305 X0 (k (k X1 X1) (k X1 X1))
       grind)
    | exact superpose eq12305 eq25796
    | (have j0 := eq25796 X0 X1 X2
       grind)
    | exact resolve eq25796 eq12305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25796
  have eq25898 : ∀ X0 X1 X2 : G, (M.op X0 (k X1 X1)) = (k (M.op X1 X2) X0) ∨ (M.op X0 (k X1 X1)) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq25859 X0 X1 X2
       have i₂ := eq236 (k X1 X1)
       grind)
    | exact superpose eq236 eq25859
    | (have j0 := eq25859 X0 X1 X2
       grind)
    | exact resolve eq25859 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25859
  have eq27808 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (k (k (M.op (k X1 X1) (M.op (M.op X0 X0) (σ x))) (M.op (k X1 X1) (M.op (M.op X0 X0) (σ x)))) (k (M.op (k X1 X1) (M.op (M.op X0 X0) (σ x))) (M.op (k X1 X1) (M.op (M.op X0 X0) (σ x))))) := by
    intro X0 X1 X2
    first
    | exact superpose eq67 eq735
    | exact resolve eq735 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27894 : ∀ X0 X2 : G, (k (k (M.op (k X0 X0) (M.op (σ x) (σ y))) (M.op (k X0 X0) (M.op (σ x) (σ y)))) (k (M.op (k X0 X0) (M.op (σ x) (σ y))) (M.op (k X0 X0) (M.op (σ x) (σ y))))) = (M.op X0 (M.op (k (k (σ x) (σ x)) (k (σ x) (σ x))) X2)) := by
    intro X0 X2
    first
    | exact superpose eq701 eq735
    | exact resolve eq735 eq701
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq701
  have eq28622 : ∀ X0 X2 : G, (k (k (M.op (k X0 X0) (M.op (σ x) (σ y))) (M.op (k X0 X0) (M.op (σ x) (σ y)))) (k (M.op (k X0 X0) (M.op (σ x) (σ y))) (M.op (k X0 X0) (M.op (σ x) (σ y))))) = (M.op X0 (k (k (M.op (σ x) (k X2 X2)) (M.op (σ x) (k X2 X2))) (k (M.op (σ x) (k X2 X2)) (M.op (σ x) (k X2 X2))))) := by
    intro X0 X2
    first
    | (have i₁ := eq27894 X0 x
       have i₂ := eq15055 sF4 x
       grind)
    | exact superpose eq15055 eq27894
    | exact resolve eq27894 eq15055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15055 eq27894
  have eq28661 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op X1 (k (k (M.op (M.op X0 X0) (σ x)) (M.op (M.op X0 X0) (σ x))) (k (M.op (M.op X0 X0) (σ x)) (M.op (M.op X0 X0) (σ x))))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq27808 X0 X0 X2
       have i₂ := eq12305 X0 (M.op (M.op X0 X0) sF4)
       grind)
    | exact superpose eq12305 eq27808
    | exact resolve eq27808 eq12305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27808
  have eq28869 : ∀ X0 : G, (M.op X0 (σ x)) = (k (k (M.op (k X0 X0) (M.op (σ x) (σ y))) (M.op (k X0 X0) (M.op (σ x) (σ y)))) (k (M.op (k X0 X0) (M.op (σ x) (σ y))) (M.op (k X0 X0) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq28622 X0 x
       have i₂ := eq14529 X0 sF4 (k x x)
       grind)
    | exact superpose eq14529 eq28622
    | exact resolve eq28622 eq14529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28622
  have eq28900 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op X1 (M.op X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28661 X0 X0 X2
       have i₂ := eq14529 X0 (M.op X0 X0) sF4
       grind)
    | exact superpose eq14529 eq28661
    | exact resolve eq28661 eq14529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28661
  have eq29019 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) := by
    intro X0
    first
    | (have i₁ := eq28869 X0
       have i₂ := eq12305 X0 sF6
       grind)
    | exact superpose eq12305 eq28869
    | exact resolve eq28869 eq12305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28869
  have eq29027 : ∀ X0 X1 X2 : G, (M.op X1 (M.op X0 X2)) = (M.op X1 (k X0 X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq28900 X0 X1 X2
       have i₂ := eq106 X0
       grind)
    | exact superpose eq106 eq28900
    | exact resolve eq28900 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28900
  have eq29322 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (k (τ (σ x)) (τ (σ x)))) := by
    intro X0
    first
    | exact superpose eq42 eq29027
    | exact resolve eq29027 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29350 : ∀ X0 : G, (M.op X0 (k (σ y) (σ y))) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq13097 eq29027
    | exact resolve eq29027 eq13097
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29351 : ∀ X0 : G, (M.op X0 (k (σ y) (σ y))) = (M.op X0 (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq3614 eq29027
    | exact resolve eq29027 eq3614
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29431 : ∀ X0 X1 : G, (k (M.op X0 X1) (M.op X0 X1)) = (M.op (M.op X0 X1) (k X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq106 (M.op X0 X1)
       have i₂ := eq29027 X0 (M.op X0 X1) X1
       grind)
    | exact superpose eq29027 eq106
    | exact resolve eq106 eq29027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq29763 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (k (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (τ (σ x)))) := by
    intro X0
    first
    | exact superpose eq1379 eq29322
    | exact resolve eq29322 eq1379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29322
  have eq33190 : (M.op (σ x) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (k (σ y) (σ y))) (σ x)) (M.op (σ x) (σ y))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq29350 eq67
    | exact resolve eq67 eq29350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq33326 : ∀ X0 X1 X2 : G, (k (k (M.op (k X0 X0) (k (σ y) (σ y))) (M.op (k X0 X0) (k (σ y) (σ y)))) (k (M.op (k X0 X0) (k (σ y) (σ y))) (M.op (k X0 X0) (k (σ y) (σ y))))) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X1) X2)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq29350 eq735
    | exact resolve eq735 eq29350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29350
  have eq33394 : ∀ X0 X1 : G, (k (k (M.op (k X0 X0) (k (σ y) (σ y))) (M.op (k X0 X0) (k (σ y) (σ y)))) (k (M.op (k X0 X0) (k (σ y) (σ y))) (M.op (k X0 X0) (k (σ y) (σ y))))) = (M.op X0 (k (M.op (M.op (σ x) (σ y)) X1) (M.op (M.op (σ x) (σ y)) X1))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq33326 X1 X1 x
       have i₂ := eq29027 (M.op sF6 X1) X1 x
       grind)
    | exact superpose eq29027 eq33326
    | exact resolve eq33326 eq29027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33326
  have eq33428 : (M.op (σ x) (σ y)) = (k (k (M.op (M.op (σ x) (σ y)) (k (σ y) (σ y))) (M.op (M.op (σ x) (σ y)) (k (σ y) (σ y)))) (k (M.op (M.op (σ x) (σ y)) (k (σ y) (σ y))) (M.op (M.op (σ x) (σ y)) (k (σ y) (σ y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq291 eq33190
    | exact resolve eq33190 eq291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq291 eq33190
  have eq33454 : ∀ X0 : G, (k (k (M.op (k X0 X0) (k (σ y) (σ y))) (M.op (k X0 X0) (k (σ y) (σ y)))) (k (M.op (k X0 X0) (k (σ y) (σ y))) (M.op (k X0 X0) (k (σ y) (σ y))))) = (M.op X0 (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq33394 X0 x
       have i₂ := eq12491 X0 sF6 x
       grind)
    | exact superpose eq12491 eq33394
    | exact resolve eq33394 eq12491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33394
  have eq33477 : (M.op (σ x) (σ y)) = (k (k (k (k (σ x) (σ x)) (k (σ x) (σ x))) (k (k (σ x) (σ x)) (k (σ x) (σ x)))) (k (k (k (σ x) (σ x)) (k (σ x) (σ x))) (k (k (σ x) (σ x)) (k (σ x) (σ x))))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq8682 eq33428
    | exact resolve eq33428 eq8682
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8682 eq33428
  have eq33497 : ∀ X0 : G, (M.op X0 (σ x)) = (k (k (M.op (k X0 X0) (k (σ y) (σ y))) (M.op (k X0 X0) (k (σ y) (σ y)))) (k (M.op (k X0 X0) (k (σ y) (σ y))) (M.op (k X0 X0) (k (σ y) (σ y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | exact superpose eq29019 eq33454
    | exact resolve eq33454 eq29019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33454
  have eq33514 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | (have i₁ := eq33477
       have i₂ := eq236 (k sF4 sF4)
       grind)
    | exact superpose eq236 eq33477
    | exact resolve eq33477 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33477
  have eq33527 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (k (k (k (σ y) (σ y)) (k (σ y) (σ y))) (k (k (σ y) (σ y)) (k (σ y) (σ y))))) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq33497 X0
       have i₂ := eq12305 X0 (k sF5 sF5)
       grind)
    | exact superpose eq12305 eq33497
    | exact resolve eq33497 eq12305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33497
  have eq33544 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq33527 X0
       have i₂ := eq236 sF5
       grind)
    | exact superpose eq236 eq33527
    | exact resolve eq33527 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33527
  have eq33826 : (M.op (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq33544 eq106
    | exact resolve eq106 eq33544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33544
  have eq34451 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq33826 eq13097
    | exact resolve eq13097 eq33826
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13097 eq33826
  have eq34511 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq34451
  have eq34592 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    first
    | exact superpose eq34511 eq33514
    | exact resolve eq33514 eq34511
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33514 eq34511
  have eq34593 : (k (σ x) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by grind
  clear eq34592
  have eq35669 : ∀ X0 X1 X2 : G, (σ y) = (M.op (k (k (σ x) (σ x)) (k (σ x) (σ x))) (M.op (M.op (M.op (k (k (σ x) (σ x)) (k (σ x) (σ x))) X0) X1) X2)) ∨ (σ (M.op x y)) = (k (σ y) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq34593 eq380
    | exact resolve eq380 eq34593
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34593
  have eq35800 : (σ (M.op x y)) = (k (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq35669 x x x
       have i₂ := eq380 sF4 x x x
       grind)
    | exact superpose eq380 eq35669
    | exact resolve eq35669 eq380
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq380 eq35669
  have eq36287 : (M.op x y) = (τ (k (σ y) (σ y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq35800 eq36
    | exact resolve eq36 eq35800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq36289 : ∀ X0 : G, (k X0 (M.op x y)) = (τ (k (σ X0) (k (σ y) (σ y)))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq35800 eq56
    | exact resolve eq56 eq35800
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56 eq35800
  have eq36371 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (τ (k (σ y) (σ y)))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq36289 x
       have i₂ := eq52 (k sF5 sF5) x
       grind)
    | exact superpose eq52 eq36289
    | exact resolve eq36289 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52 eq36289
  have eq36373 : (M.op x y) = (k (τ (σ y)) (τ (σ y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq36287
       have i₂ := eq116 sF5 sF5
       grind)
    | exact superpose eq116 eq36287
    | exact resolve eq36287 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36287
  have eq36386 : ∀ X0 : G, (k X0 (M.op x y)) = (k X0 (k (τ (σ y)) (τ (σ y)))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq36371 X0
       have i₂ := eq116 sF5 sF5
       grind)
    | exact superpose eq116 eq36371
    | exact resolve eq36371 eq116
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq36371
  have eq37229 : ∀ X0 : G, (M.op (M.op (k X0 X0) (τ (σ y))) (M.op x y)) = X0 ∨ (σ x) = (σ y) := by
    intro X0
    first
    | exact superpose eq36373 eq235
    | exact resolve eq235 eq36373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq235
  have eq37231 : (τ (σ y)) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq36373 eq236
    | exact resolve eq236 eq36373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq41760 : (τ (σ y)) = (M.op (M.op (M.op x y) (τ (σ y))) (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq36373 eq37229
    | exact resolve eq37229 eq36373
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36373 eq37229
  have eq41858 : (τ (σ y)) = (M.op (M.op (M.op x y) (τ (σ y))) (M.op x y)) ∨ (σ x) = (σ y) := by grind
  clear eq41760
  have eq42002 : ∀ X0 X1 : G, (M.op X0 (M.op (τ (σ y)) X1)) = (k (k (M.op (k X0 X0) (M.op (M.op x y) (τ (σ y)))) (M.op (k X0 X0) (M.op (M.op x y) (τ (σ y))))) (k (M.op (k X0 X0) (M.op (M.op x y) (τ (σ y)))) (M.op (k X0 X0) (M.op (M.op x y) (τ (σ y)))))) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | exact superpose eq41858 eq735
    | exact resolve eq735 eq41858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41858
  have eq42042 : ∀ X0 X1 : G, (M.op X0 (M.op (τ (σ y)) X1)) = (M.op X0 (k (k (M.op (M.op x y) (τ (σ y))) (M.op (M.op x y) (τ (σ y)))) (k (M.op (M.op x y) (τ (σ y))) (M.op (M.op x y) (τ (σ y)))))) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq42002 X0 X1
       have i₂ := eq12305 X0 (M.op sF2 (τ sF5))
       grind)
    | exact superpose eq12305 eq42002
    | exact resolve eq42002 eq12305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42002
  have eq42092 : ∀ X0 X1 : G, (M.op X0 (M.op x y)) = (M.op X0 (M.op (τ (σ y)) X1)) ∨ (σ x) = (σ y) := by
    intro X0 X1
    first
    | (have i₁ := eq42042 X0 X1
       have i₂ := eq14529 X0 sF2 (τ sF5)
       grind)
    | exact superpose eq14529 eq42042
    | exact resolve eq42042 eq14529
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14529 eq42042
  have eq42120 : ∀ X0 : G, (M.op X0 (M.op x y)) = (M.op X0 (k (τ (σ y)) (τ (σ y)))) ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq42092 x x
       have i₂ := eq29027 (τ sF5) x x
       grind)
    | exact superpose eq29027 eq42092
    | exact resolve eq42092 eq29027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42092
  have eq42918 : (σ y) = (σ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq37231 eq35
    | exact resolve eq35 eq37231
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37231
  have eq42922 : (σ y) = (k (σ (k (M.op x y) (M.op x y))) (σ (k (M.op x y) (M.op x y)))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq42918
       have i₂ := eq15 (k sF2 sF2) (k sF2 sF2)
       grind)
    | exact superpose eq15 eq42918
    | exact resolve eq42918 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42918
  have eq42936 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq42922
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq42922
    | exact resolve eq42922 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42922
  have eq42947 : (σ y) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq42936
    | exact resolve eq42936 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42936
  have eq66374 : ∀ X0 X1 X2 : G, (k (k (M.op (k X0 X0) (k (σ y) (σ y))) (M.op (k X0 X0) (k (σ y) (σ y)))) (k (M.op (k X0 X0) (k (σ y) (σ y))) (M.op (k X0 X0) (k (σ y) (σ y))))) = (M.op X0 (M.op (M.op (M.op (σ x) (σ y)) X1) X2)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq29351 eq735
    | exact resolve eq735 eq29351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq735 eq29351
  have eq66474 : ∀ X0 X1 : G, (k (k (M.op (k X0 X0) (k (σ y) (σ y))) (M.op (k X0 X0) (k (σ y) (σ y)))) (k (M.op (k X0 X0) (k (σ y) (σ y))) (M.op (k X0 X0) (k (σ y) (σ y))))) = (M.op X0 (k (M.op (M.op (σ x) (σ y)) X1) (M.op (M.op (σ x) (σ y)) X1))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    intro X0 X1
    first
    | (have i₁ := eq66374 X1 X1 x
       have i₂ := eq29027 (M.op sF6 X1) X1 x
       grind)
    | exact superpose eq29027 eq66374
    | exact resolve eq66374 eq29027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66374
  have eq66552 : ∀ X0 : G, (k (k (M.op (k X0 X0) (k (σ y) (σ y))) (M.op (k X0 X0) (k (σ y) (σ y)))) (k (M.op (k X0 X0) (k (σ y) (σ y))) (M.op (k X0 X0) (k (σ y) (σ y))))) = (M.op X0 (k (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) (k (M.op (σ x) (σ y)) (M.op (σ x) (σ y))))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq66474 X0 x
       have i₂ := eq12491 X0 sF6 x
       grind)
    | exact superpose eq12491 eq66474
    | exact resolve eq66474 eq12491
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12491 eq66474
  have eq66608 : ∀ X0 : G, (M.op X0 (σ x)) = (k (k (M.op (k X0 X0) (k (σ y) (σ y))) (M.op (k X0 X0) (k (σ y) (σ y)))) (k (M.op (k X0 X0) (k (σ y) (σ y))) (M.op (k X0 X0) (k (σ y) (σ y))))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq29019 eq66552
    | exact resolve eq66552 eq29019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29019 eq66552
  have eq66645 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (k (k (k (σ y) (σ y)) (k (σ y) (σ y))) (k (k (σ y) (σ y)) (k (σ y) (σ y))))) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq66608 X0
       have i₂ := eq12305 X0 (k sF5 sF5)
       grind)
    | exact superpose eq12305 eq66608
    | exact resolve eq66608 eq12305
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12305 eq66608
  have eq66665 : ∀ X0 : G, (M.op X0 (σ x)) = (M.op X0 (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq66645 X0
       have i₂ := eq236 sF5
       grind)
    | exact superpose eq236 eq66645
    | exact resolve eq66645 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66645
  have eq67758 : (M.op (σ y) (σ x)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq66665 eq106
    | exact resolve eq106 eq66665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66665
  have eq69476 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq67758 eq3614
    | exact resolve eq3614 eq67758
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3614 eq67758
  have eq69556 : (M.op (σ x) (σ y)) = (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by grind
  clear eq69476
  have eq69622 : (σ (M.op x y)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq69556 eq33
    | exact resolve eq33 eq69556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69556
  have eq70963 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (k (σ y) (σ x)) = (k (σ x) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | exact superpose eq3598 eq69622
    | exact resolve eq69622 eq3598
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3598 eq69622
  have eq70968 : (k (σ y) (σ x)) ≠ (k (σ y) (σ y)) ∨ (σ (M.op x y)) = (k (σ x) (σ y)) := by
    first
    | (have r₁ := eq70963
       have r₂ := eq3613
       grind)
    | exact resolve eq70963 eq3613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3613 eq70963
  have eq87480 : ∀ X0 X1 X2 X3 : G, (k (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) = (M.op (k X0 X0) (M.op (k X1 X1) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq236 (M.op (k X0 X0) (M.op (k X1 X1) X2))
       have i₂ := eq743 X0 X1 X2 X3
       grind)
    | exact superpose eq743 eq236
    | exact resolve eq236 eq743
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq743
  have eq87820 : ∀ X0 X1 X2 : G, (M.op (k X0 X0) (k (k X1 X1) (k X1 X1))) = (k (M.op X0 (M.op X1 X2)) (M.op X0 (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq87480 X0 X1 X2 x
       have i₂ := eq29027 (k X1 X1) (k X0 X0) x
       grind)
    | exact superpose eq29027 eq87480
    | exact resolve eq87480 eq29027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87480
  have eq88588 : ∀ X0 X1 : G, (M.op (k X0 X0) (k (k X1 X1) (k X1 X1))) = (k (M.op X0 (k X1 X1)) (M.op X0 (k X1 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq87820 X1 X0 x
       have i₂ := eq29027 X0 X1 x
       grind)
    | exact superpose eq29027 eq87820
    | exact resolve eq87820 eq29027
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29027 eq87820
  have eq229832 : ∀ X0 : G, (k (M.op x y) X0) = (M.op X0 (k (τ (σ x)) (τ (σ x)))) ∨ (M.op (M.op x y) X0) = (M.op X0 (k (τ (σ x)) (τ (σ x)))) := by
    intro X0
    first
    | exact superpose eq42 eq25898
    | exact resolve eq25898 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq25898
  have eq230295 : ∀ X0 : G, (k (M.op x y) X0) = (M.op X0 (k (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (τ (σ x)))) ∨ (M.op (M.op x y) X0) = (M.op X0 (k (τ (σ x)) (τ (σ x)))) := by
    intro X0
    first
    | exact superpose eq1379 eq229832
    | (have j0 := eq229832 X0
       grind)
    | exact resolve eq229832 eq1379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229832
  have eq230355 : ∀ X0 : G, (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ (M.op (M.op x y) X0) = (M.op X0 (k (τ (σ x)) (τ (σ x)))) := by
    intro X0
    first
    | exact superpose eq29763 eq230295
    | (have j0 := eq230295 X0
       grind)
    | exact resolve eq230295 eq29763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230295
  have eq230385 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op X0 (k (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) (τ (σ x)))) ∨ (k (M.op x y) X0) = (M.op X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1379 eq230355
    | (have j0 := eq230355 X0
       grind)
    | exact resolve eq230355 eq1379
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1379 eq230355
  have eq230398 : ∀ X0 : G, (k (M.op x y) X0) = (M.op X0 (M.op x y)) ∨ (M.op X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | exact superpose eq29763 eq230385
    | (have j0 := eq230385 X0
       grind)
    | exact resolve eq230385 eq29763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29763 eq230385
  have eq230695 : ∀ X0 : G, (k (M.op x y) X0) ≠ (M.op (M.op x y) X0) ∨ (M.op X0 (M.op x y)) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have j0 := eq230398 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230398
  have eq231161 : (M.op (M.op x y) (M.op x y)) ≠ (k (M.op x y) (k (τ (σ y)) (τ (σ y)))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (k (τ (σ y)) (τ (σ y))) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq42120 eq230695
    | exact resolve eq230695 eq42120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42120 eq230695
  have eq231185 : (k (M.op x y) (M.op x y)) ≠ (k (M.op x y) (k (τ (σ y)) (τ (σ y)))) ∨ (M.op (M.op x y) (M.op x y)) = (M.op (k (τ (σ y)) (τ (σ y))) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq231161
       have i₂ := eq106 sF2
       grind)
    | exact superpose eq106 eq231161
    | exact resolve eq231161 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231161
  have eq231194 : (M.op (M.op x y) (M.op x y)) = (M.op (k (τ (σ y)) (τ (σ y))) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq231185
       have r₂ := eq36386 (M.op x y)
       grind)
    | exact resolve eq231185 eq36386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36386 eq231185
  have eq231199 : (k (M.op x y) (M.op x y)) = (M.op (k (τ (σ y)) (τ (σ y))) (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq231194
       have i₂ := eq106 sF2
       grind)
    | exact superpose eq106 eq231194
    | exact resolve eq231194 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq231194
  have eq231283 : (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) = (M.op (k (M.op x y) (M.op x y)) (k (k (τ (σ y)) (τ (σ y))) (k (τ (σ y)) (τ (σ y))))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq231199 eq29431
    | exact resolve eq29431 eq231199
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29431 eq231199
  have eq231291 : (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) = (k (M.op (M.op x y) (k (τ (σ y)) (τ (σ y)))) (M.op (M.op x y) (k (τ (σ y)) (τ (σ y))))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq231283
       have i₂ := eq88588 sF2 (τ sF5)
       grind)
    | exact superpose eq88588 eq231283
    | exact resolve eq231283 eq88588
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq88588 eq231283
  have eq231339 : (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) = (k (k (k (τ (σ x)) (τ (σ x))) (k (τ (σ x)) (τ (σ x)))) (k (k (τ (σ x)) (τ (σ x))) (k (τ (σ x)) (τ (σ x))))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1161 eq231291
    | exact resolve eq231291 eq1161
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1161 eq231291
  have eq231358 : (τ (σ x)) = (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq231339
       have i₂ := eq236 (τ sF4)
       grind)
    | exact superpose eq236 eq231339
    | exact resolve eq231339 eq236
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq236 eq231339
  have eq232049 : (σ x) = (σ (k (k (M.op x y) (M.op x y)) (k (M.op x y) (M.op x y)))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq231358 eq35
    | exact resolve eq35 eq231358
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq231358
  have eq232055 : (σ x) = (k (σ (k (M.op x y) (M.op x y))) (σ (k (M.op x y) (M.op x y)))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq232049
       have i₂ := eq15 (k sF2 sF2) (k sF2 sF2)
       grind)
    | exact superpose eq15 eq232049
    | exact resolve eq232049 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232049
  have eq232064 : (σ x) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq232055
       have i₂ := eq15 sF2 sF2
       grind)
    | exact superpose eq15 eq232055
    | exact resolve eq232055 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232055
  have eq232070 : (σ x) = (k (k (σ (M.op x y)) (σ (M.op x y))) (k (σ (M.op x y)) (σ (M.op x y)))) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq26 eq232064
    | exact resolve eq232064 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq232064
  have eq232115 : (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq232070 eq42947
    | exact resolve eq42947 eq232070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42947 eq232070
  have eq232266 : (σ x) = (σ y) := by grind
  clear eq232115
  have eq232790 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq232266 eq4628
    | exact resolve eq4628 eq232266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4628
  have eq232905 : (k (σ x) (σ x)) ≠ (k (σ x) (σ x)) ∨ (σ (M.op x y)) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq232266 eq70968
    | exact resolve eq70968 eq232266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70968 eq232266
  have eq232957 : (σ (M.op x y)) = (k (σ x) (σ x)) := by grind
  clear eq232905
  have eq232960 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq232790
  have eq233041 : (M.op (σ x) (σ y)) = (k (σ x) (σ x)) := by
    first
    | (have i₁ := eq232960
       have i₂ := eq106 sF4
       grind)
    | exact superpose eq106 eq232960
    | exact resolve eq232960 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq232960
  have eq233886 : (σ (M.op x y)) ≠ (k (σ x) (σ x)) := by
    first
    | exact superpose eq233041 eq33
    | exact resolve eq33 eq233041
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33 eq233041
  have eq233937 : False := by grind
  exact eq233937

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(X,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyy_pxy_pxx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq13 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq44 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq44 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq58 : ∀ X0 X1 : G, (M.op X1 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
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
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq50 X0 X1
       have i₂ := eq26 X1
       grind)
    | exact superpose eq26 eq50
    | (have j0 := eq50 X0 X1
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq62 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
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
  clear eq26 eq51
  have eq65 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq62 X0 X1
       have j1 := eq61 X0 X1
       grind)
    | (have r₁ := eq62 X0 X1
       have r₂ := eq61 X0 X1
       grind)
    | exact resolve eq62 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq62
  have eq158 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq253 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X3) (M.op X3 X4)) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq9 (M.op X0 X0) X3 X4
       have i₂ := eq19 X0 X1 X2
       grind)
    | (have i₁ := eq9 (M.op X2 X2) X1 X2
       have i₂ := eq19 X2 X2 X2
       grind)
    | exact superpose eq19 eq9
    | exact resolve eq9 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq2897 : ∀ X0 X1 X2 X3 X4 : G, (M.op X0 X1) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X3) (M.op X3 X4)) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq253 X0 X1 X2 X3 X4
       have i₂ := eq65 X0 X1
       grind)
    | (have i₁ := eq253 X1 X1 X2 X3 X4
       have i₂ := eq65 X0 X1
       grind)
    | exact superpose eq65 eq253
    | (have j1 := eq65 X0 X1
       grind)
    | exact resolve eq253 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq3022 : ∀ X0 X1 X2 X3 X4 X5 : G, (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) X3) (M.op X3 X4)) ≠ (M.op X0 X5) ∨ (M.op X0 X5) = (k X0 X5) := by
    intro X0 X1 X2 X3 X4 X5
    first
    | (have i₁ := eq158 X0 X5
       have i₂ := eq253 X0 X1 X2 X3 X4
       grind)
    | exact superpose eq253 eq158
    | (have j0 := eq158 X0 X5
       grind)
    | exact resolve eq158 eq253
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq158 eq253
  have eq3219 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2897 X0 X1 x x x
       have j1 := eq3022 X0 X1 x x x X1
       grind)
    | (have r₁ := eq2897 X0 X1 x x x
       have r₂ := eq3022 X0 X1 x x x X1
       grind)
    | exact resolve eq2897 eq3022
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2897 eq3022
  have eq89920 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq3219 (σ X0) (σ X1)
       grind)
    | exact superpose eq3219 eq15
    | exact resolve eq15 eq3219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq89939 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq89920 X0 X1
       have i₂ := eq3219 X0 X1
       grind)
    | exact superpose eq3219 eq89920
    | exact resolve eq89920 eq3219
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3219 eq89920
  have eq89967 : False := by grind
  exact eq89967

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,Y) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyy_pxy_pyx_pxy_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq9 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X1 X1) (M.op (M.op X0 X0) X2)) X0) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 X1 (M.op (M.op X0 X0) X2) (M.op X2 x)
       have i₂ := eq9 X0 X2 x
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq32 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
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
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) = X1 ∨ (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X1 X2 X3
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq9 X1 X1 X2
       have i₂ := eq14 X1 X1
       grind)
    | exact superpose eq14 eq9
    | (have j1 := eq14 X0 X1
       grind)
    | exact resolve eq9 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq32 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq46 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq45 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq52 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) (M.op X2 X3)) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq38 X0 X1 X2 X3
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X0 (M.op X2 X3) X2 X3
       have r₂ := eq12 (M.op X2 X3) (M.op (M.op X0 (M.op X2 X3)) X2)
       grind)
    | (have r₁ := eq38 X0 X1 X2 X3
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq58 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = (k X1 X0) := by
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
  have eq132 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq58 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq58
    | exact resolve eq58 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq58 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58
  have eq215 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X3 X3) (M.op (M.op X0 X1) (M.op X1 X2))) X0) = X3 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq21 X0 X3 (M.op X0 X0)
       have i₂ := eq19 X0 X1 X2
       grind)
    | (have i₁ := eq21 X1 X1 (M.op X1 X2)
       have i₂ := eq19 X1 X1 X2
       grind)
    | exact superpose eq19 eq21
    | exact resolve eq21 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq21
  have eq351 : ∀ X0 X1 X2 X3 : G, (σ X1) = (M.op (M.op (M.op (σ X0) (σ X1)) X2) (M.op X2 X3)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq52 (σ X0) (σ X1) X2 X3
       grind)
    | exact superpose eq52 eq15
    | (have j1 := eq52 (σ X0) (σ X1) X2 X3
       grind)
    | exact resolve eq15 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2378 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq215 X1 X0 x (M.op X1 X0)
       have i₂ := eq52 X1 X0 (M.op X1 X0) (M.op X0 x)
       grind)
    | exact superpose eq52 eq215
    | (have j1 := eq52 X1 X0 x x
       grind)
    | exact resolve eq215 eq52
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq2428 : ∀ X0 X1 : G, (M.op X1 X0) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2378 X0 X1
       have j1 := eq140 X1 X0
       grind)
    | (have r₁ := eq2378 X0 X1
       have r₂ := eq140 X0 X1
       grind)
    | (have r₁ := eq2378 X1 X0
       have r₂ := eq140 X0 X1
       grind)
    | exact resolve eq2378 eq140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq2378
  have eq3409 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq132 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq132
  have eq3410 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq3409 X0 X1
       have i₂ := eq2428 X1 X0
       grind)
    | exact superpose eq2428 eq3409
    | (have j0 := eq3409 X0 X1
       grind)
    | exact resolve eq3409 eq2428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3409
  have eq6675 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq215 (σ X1) (σ X0) x (M.op (σ X1) (σ X0))
       have i₂ := eq351 X1 X0 (M.op (σ X1) (σ X0)) (M.op (σ X0) x)
       grind)
    | exact superpose eq351 eq215
    | (have j1 := eq351 X1 X0 x x
       grind)
    | exact resolve eq215 eq351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215 eq351
  have eq6809 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq6675 X0 X1
       have i₂ := eq2428 X0 X1
       grind)
    | exact superpose eq2428 eq6675
    | (have j0 := eq6675 X0 X1
       grind)
    | exact resolve eq6675 eq2428
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2428 eq6675
  have eq6932 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq6809 X0 X1
       have j1 := eq3410 X1 X0
       grind)
    | (have r₁ := eq6809 X0 X1
       have r₂ := eq3410 X0 X1
       grind)
    | (have r₁ := eq6809 X1 X0
       have r₂ := eq3410 X0 X1
       grind)
    | exact resolve eq6809 eq3410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3410 eq6809
  have eq6996 : False := by grind
  exact eq6996

/-- `Equation2045`: `x = ((x ◇ x) ◇ y) ◇ (y ◇ z)`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyx_pyy_pxx_pyy_pyx_Equation2045 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law2045 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law2045.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X0) X1) (M.op X1 X2)) = X0 := by
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
  have eq30 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq16
    | (have j0 := eq16 (M.op x y)
       grind)
    | exact resolve eq16 eq20
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
  have eq50 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 X1) (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14 (M.op (M.op X0 X0) (M.op X0 X0)) X1 X2
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq52 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) x) (M.op x y)) = X0 := by
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
  have eq53 : ∀ X0 : G, (M.op (M.op (M.op X0 X0) (σ x)) (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : y ≠ (M.op x y) ∨ (M.op y y) = (k y x) := by
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
  have eq65 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq73 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq74 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq76 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq86 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq73
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq73 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq16
    | exact resolve eq16 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq92 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
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
  have eq93 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq92
    | exact resolve eq92 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq94 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq93
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq93
    | exact resolve eq93 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq95 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq94
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq94
    | exact resolve eq94 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94
  have eq100 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (k y y)
       have i₂ := eq74
       grind)
    | exact superpose eq74 eq16
    | exact resolve eq16 eq74
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : (M.op x y) ≠ (M.op x x) ∨ y = (M.op x y) ∨ (k y x) = (M.op x x) := by
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
  have eq108 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (k (σ y) (σ x)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq111 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq112 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq111 X0
       have j1 := eq13 X0 X0
       grind)
    | (have r₁ := eq111 X0
       have r₂ := eq13 X0 X0
       grind)
    | exact resolve eq111 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq114 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq112 (σ X0)
       grind)
    | exact superpose eq112 eq10
    | exact resolve eq10 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq115 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq112 x
       grind)
    | exact superpose eq112 eq43
    | exact resolve eq43 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq116 : (k (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq112 y
       grind)
    | exact superpose eq112 eq74
    | exact resolve eq74 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq117 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq112 sF2
       grind)
    | exact superpose eq112 eq49
    | exact resolve eq49 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq118 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq117
       have i₂ := eq112 x
       grind)
    | exact superpose eq112 eq117
    | exact resolve eq117 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq119 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq116
       have i₂ := eq112 sF3
       grind)
    | exact superpose eq112 eq116
    | exact resolve eq116 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116
  have eq120 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq115
       have i₂ := eq112 sF2
       grind)
    | exact superpose eq112 eq115
    | exact resolve eq115 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq115
  have eq121 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq114 X0
       have i₂ := eq112 X0
       grind)
    | exact superpose eq112 eq114
    | exact resolve eq114 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq114
  have eq128 : (k y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq100
       have i₂ := eq112 sF3
       grind)
    | exact superpose eq112 eq100
    | exact resolve eq100 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq129 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq128
       have i₂ := eq112 y
       grind)
    | exact superpose eq112 eq128
    | exact resolve eq128 eq112
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112 eq128
  have eq254 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq52
    | exact resolve eq52 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq257 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op (M.op X0 X0) (M.op X0 X0))
       have i₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq512 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ (M.op X0 X0)) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq52 (σ X0)
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq52
    | exact resolve eq52 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq665 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X0) X3) (M.op X3 X4)) = (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq50 (M.op X0 X0) X1 X2
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq50 (M.op X2 X2) X1 X2
       have i₂ := eq50 X2 X2 X2
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X0 X0) (M.op X0 X0)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq50 (M.op X0 X1) (M.op X1 X2) X3
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq50 (M.op X0 X0) (M.op X0 X0) X2
       have i₂ := eq50 X0 X1 X2
       grind)
    | exact superpose eq50 eq50
    | exact resolve eq50 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq677 : ∀ X0 : G, (M.op (M.op x x) (M.op x x)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq50 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq50
    | (have j0 := eq50 x y X0
       grind)
    | exact resolve eq50 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq678 : ∀ X0 : G, (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | exact superpose eq26 eq50
    | (have j0 := eq50 (σ x) (σ y) X0
       grind)
    | exact resolve eq50 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq694 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X0) X3)) = X0 := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X0 (M.op X0 X0) X3
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq14 X1 (M.op X1 X2) X2
       have i₂ := eq50 X1 X1 X2
       grind)
    | exact superpose eq50 eq14
    | exact resolve eq14 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq699 : ∀ X0 X1 X2 : G, (M.op X0 X0) = (M.op (M.op (M.op (M.op X0 X1) (M.op X1 X2)) x) (M.op x y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq52 (M.op X0 X0)
       have i₂ := eq50 X0 X1 X2
       grind)
    | (have i₁ := eq52 (M.op X2 X2)
       have i₂ := eq50 X2 X2 X2
       grind)
    | exact superpose eq50 eq52
    | exact resolve eq52 eq50
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq720 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op X0 X1) (M.op X1 X2)) (M.op (M.op X0 X1) (M.op X1 X2))) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq665 X0 X1 X2 x x
       have i₂ := eq14 X0 x x
       grind)
    | exact superpose eq14 eq665
    | exact resolve eq665 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq665
  have eq964 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq76 X0 X1
       have i₂ := eq121 X1
       grind)
    | exact superpose eq121 eq76
    | (have j0 := eq76 X0 X1
       grind)
    | exact resolve eq76 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq1058 : ∀ X0 X1 X2 : G, (M.op (M.op (σ X1) (σ X1)) (M.op (σ X1) (σ X1))) = (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq50 (σ X1) (σ X0) X2
       have i₂ := eq964 X0 X1
       grind)
    | exact superpose eq964 eq50
    | (have j1 := eq964 X0 X1
       grind)
    | exact resolve eq50 eq964
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq1062 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X0 X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X0 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq964 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq964
  have eq1066 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) = (M.op (σ (M.op X1 X1)) (σ (M.op X1 X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1058 X0 X0 X2
       have i₂ := eq121 X0
       grind)
    | exact superpose eq121 eq1058
    | (have j0 := eq1058 X0 X1 X2
       grind)
    | exact resolve eq1058 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1058
  have eq1087 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) = (σ (M.op (M.op X1 X1) (M.op X1 X1))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1066 X0 X1 X2
       have i₂ := eq121 (M.op X1 X1)
       grind)
    | exact superpose eq121 eq1066
    | (have j0 := eq1066 X0 X1 X2
       grind)
    | exact resolve eq1066 eq121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121 eq1066
  have eq1488 : ∀ X0 : G, (M.op (M.op X0 x) (M.op x y)) = (M.op (M.op X0 (σ x)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq257 X0
       have i₂ := eq254 X0
       grind)
    | exact superpose eq254 eq257
    | exact resolve eq257 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq257
  have eq1499 : ∀ X0 : G, (σ x) = (M.op (M.op (M.op (σ x) x) (M.op x y)) (M.op (M.op (σ x) (σ y)) X0)) := by
    intro X0
    first
    | exact superpose eq1488 eq14
    | exact resolve eq14 eq1488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1488
  have eq1677 : ∀ X0 : G, (M.op (M.op x x) (M.op x y)) = (M.op (M.op x y) (M.op y X0)) := by
    intro X0
    first
    | (have i₁ := eq677 X0
       have i₂ := eq254 x
       grind)
    | exact superpose eq254 eq677
    | exact resolve eq677 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq677
  have eq1683 : ∀ X0 X1 : G, x = (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x y) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1677 eq14
    | exact resolve eq14 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1743 : ∀ X0 : G, (σ (M.op (M.op x y) (M.op y X0))) = (M.op (M.op (σ x) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq1683 eq512
    | exact resolve eq512 eq1683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq512
  have eq1756 : ∀ X0 : G, (M.op (M.op (σ x) x) (M.op x y)) = (σ (M.op (M.op x y) (M.op y X0))) := by
    intro X0
    first
    | (have i₁ := eq1743 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq1743
    | (have j0 := eq1743 X0
       grind)
    | exact resolve eq1743 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1743
  have eq1761 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) = (M.op (M.op (σ x) x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq678 X0
       have i₂ := eq254 sF2
       grind)
    | exact superpose eq254 eq678
    | exact resolve eq678 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq678
  have eq1771 : ∀ X0 X1 : G, (σ x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) X1)) := by
    intro X0 X1
    first
    | exact superpose eq1761 eq1499
    | exact resolve eq1499 eq1761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1499 eq1761
  have eq8405 : (σ (M.op (M.op x x) (M.op x y))) = (M.op (M.op (σ x) x) (M.op x y)) := by
    first
    | exact superpose eq1677 eq1756
    | exact resolve eq1756 eq1677
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1677 eq1756
  have eq11244 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq95 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11245 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq11244
    | exact resolve eq11244 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11244
  have eq11256 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11245
       have r₂ := eq27
       grind)
    | exact resolve eq11245 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11245
  have eq11260 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq11256
    | exact resolve eq11256 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11256
  have eq11262 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq11260
    | exact resolve eq11260 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11260
  have eq11264 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11262 eq108
    | (have r₁ := eq108
       have r₂ := eq11262
       grind)
    | exact resolve eq108 eq11262
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11262
  have eq11338 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq11264
  have eq11339 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by grind
  clear eq11338
  have eq11546 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq11339 eq95
    | exact resolve eq95 eq11339
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95 eq11339
  have eq11554 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11546
  have eq11556 : (M.op x y) = (M.op x x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11554
       have r₂ := eq27
       grind)
    | exact resolve eq11554 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11554
  have eq11558 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq107
       have i₂ := eq11556
       grind)
    | exact superpose eq11556 eq107
    | (have r₁ := eq107
       have r₂ := eq11556
       grind)
    | exact resolve eq107 eq11556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11559 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq120
       have i₂ := eq11556
       grind)
    | exact superpose eq11556 eq120
    | exact resolve eq120 eq11556
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11556
  have eq11638 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11558
  have eq11639 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11638
  have eq11667 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq11559
    | exact resolve eq11559 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11559
  have eq11875 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq11639
       grind)
    | exact superpose eq11639 eq73
    | exact resolve eq73 eq11639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11639
  have eq11889 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq11875
    | exact resolve eq11875 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11875
  have eq12007 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq11889 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq11889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11889
  have eq12010 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12007
    | exact resolve eq12007 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12007
  have eq12021 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq12010
       have r₂ := eq27
       grind)
    | exact resolve eq12010 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12010
  have eq12025 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12021
    | exact resolve eq12021 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12021
  have eq12027 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq12025
    | exact resolve eq12025 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12025
  have eq12028 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq12027
  have eq12238 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12028 eq11667
    | exact resolve eq11667 eq12028
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11667 eq12028
  have eq12306 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq12238
  have eq12343 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq12306
       have r₂ := eq27
       grind)
    | exact resolve eq12306 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12306
  have eq12349 : (σ y) ≠ (σ y) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12343 eq65
    | (have r₁ := eq65
       have r₂ := eq12343
       grind)
    | exact resolve eq65 eq12343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq12343
  have eq12366 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq12349
  have eq12570 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ y = (M.op x y) := by
    first
    | exact superpose eq12366 eq91
    | exact resolve eq91 eq12366
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq12366
  have eq12594 : (M.op y y) = (k y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq129 eq12570
    | exact resolve eq12570 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq129 eq12570
  have eq12597 : (M.op y y) = (k y x) := by
    first
    | (have r₁ := eq12594
       have r₂ := eq64
       grind)
    | exact resolve eq12594 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq12594
  have eq12603 : (k (σ y) (σ x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq73
       have i₂ := eq12597
       grind)
    | exact superpose eq12597 eq73
    | exact resolve eq73 eq12597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12611 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq12597
       grind)
    | exact superpose eq12597 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq12597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq12612 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12611
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12611
    | exact resolve eq12611 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12611
  have eq12619 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12603
       have i₂ := eq119
       grind)
    | exact superpose eq119 eq12603
    | exact resolve eq12603 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119 eq12603
  have eq12621 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12612
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12612
    | exact resolve eq12612 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12612
  have eq12623 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq12621
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq12621
    | exact resolve eq12621 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12621
  have eq14365 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x y) (M.op y X0))) ∨ (M.op x y) = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq720 y y x
       have i₂ := eq12623
       grind)
    | exact superpose eq12623 eq720
    | exact resolve eq720 eq12623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12623
  have eq14376 : (M.op x y) = (M.op x x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | exact superpose eq1683 eq14365
    | exact resolve eq14365 eq1683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14365
  have eq14400 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq107
       have i₂ := eq14376
       grind)
    | exact superpose eq14376 eq107
    | (have r₁ := eq107
       have r₂ := eq14376
       grind)
    | exact resolve eq107 eq14376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq14376
  have eq14482 : (M.op x y) ≠ (M.op x y) ∨ y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = y := by grind
  clear eq14400
  have eq14483 : y = (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = y := by grind
  clear eq14482
  have eq14512 : (M.op x y) = (M.op y y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq14483
       have i₂ := eq12597
       grind)
    | exact superpose eq12597 eq14483
    | exact resolve eq14483 eq12597
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12597 eq14483
  have eq14815 : ∀ X0 : G, y = (M.op (M.op (M.op x y) (M.op y X0)) (M.op (M.op x y) (M.op y X0))) ∨ y = (M.op x y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq720 y y x
       have i₂ := eq14512
       grind)
    | exact superpose eq14512 eq720
    | exact resolve eq720 eq14512
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14512
  have eq14826 : x = y ∨ y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq1683 eq14815
    | exact resolve eq14815 eq1683
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1683 eq14815
  have eq14827 : y = (M.op x y) ∨ x = y := by grind
  clear eq14826
  have eq14852 : (σ y) = (σ (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq14827 eq20
    | exact resolve eq20 eq14827
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq14989 : (σ (M.op x y)) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq14852
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq14852
    | exact resolve eq14852 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14852
  have eq16682 : (k (σ y) (σ x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq1062 x y
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq1062
    | (have j0 := eq1062 x y
       grind)
    | exact resolve eq1062 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1062
  have eq16723 : (k (σ y) (σ x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16682
       have i₂ := eq120
       grind)
    | exact superpose eq120 eq16682
    | exact resolve eq16682 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16682
  have eq16792 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12619 eq16723
    | exact resolve eq16723 eq12619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16723
  have eq16858 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16792
       have i₂ := eq120
       grind)
    | exact superpose eq120 eq16792
    | exact resolve eq16792 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16792
  have eq16910 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16858
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16858
    | exact resolve eq16858 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16858
  have eq16956 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16910
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq16910
    | exact resolve eq16910 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16910
  have eq16999 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq16956
    | exact resolve eq16956 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16956
  have eq17038 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16999
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq16999
    | exact resolve eq16999 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16999
  have eq17047 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq17038
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq17038
    | exact resolve eq17038 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17038
  have eq17052 : (M.op (σ y) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq17047
    | exact resolve eq17047 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17047
  have eq18009 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) (M.op (M.op X0 X1) (M.op X0 X1))) = (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq675 X0 X1 X2 X3
       have i₂ := eq254 X0
       grind)
    | exact superpose eq254 eq675
    | exact resolve eq675 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675
  have eq18010 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) x) (M.op x y)) = (M.op (M.op (M.op X0 x) (M.op x y)) (M.op (M.op X1 X2) X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq18009 X0 X1 X2 X3
       have i₂ := eq254 (M.op X0 X1)
       grind)
    | exact superpose eq254 eq18009
    | exact resolve eq18009 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18009
  have eq23487 : ∀ X0 X1 X2 : G, (M.op (σ (k X0 X1)) (M.op (σ X0) X2)) = (σ (M.op (M.op X1 x) (M.op x y))) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq1087 X0 X1 X2
       have i₂ := eq254 X1
       grind)
    | exact superpose eq254 eq1087
    | (have j0 := eq1087 X0 X1 X2
       grind)
    | exact resolve eq1087 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1087
  have eq23980 : ∀ X0 : G, (σ (M.op (M.op x x) (M.op x y))) = (M.op (k (σ y) (σ x)) (M.op (σ y) X0)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq23487 y x X0
       have i₂ := eq73
       grind)
    | exact superpose eq73 eq23487
    | (have j0 := eq23487 y x x
       grind)
    | exact resolve eq23487 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq23487
  have eq24203 : ∀ X0 : G, (σ (M.op (M.op x x) (M.op x y))) = (M.op (k (σ y) (σ x)) (M.op (σ y) X0)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq23980 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq23980
    | (have j0 := eq23980 X0
       grind)
    | exact resolve eq23980 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23980
  have eq24347 : ∀ X0 : G, (σ (M.op (M.op x x) (M.op x y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) X0)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq12619 eq24203
    | exact resolve eq24203 eq12619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24203
  have eq24470 : ∀ X0 : G, (M.op (M.op (σ x) x) (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) X0)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq8405 eq24347
    | exact resolve eq24347 eq8405
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8405 eq24347
  have eq24590 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (σ x) x) (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq24470 X0
       have i₂ := eq120
       grind)
    | exact superpose eq120 eq24470
    | (have j0 := eq24470 X0
       grind)
    | exact resolve eq24470 eq120
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120 eq24470
  have eq24688 : ∀ X0 : G, (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) x) (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq24590 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24590
    | (have j0 := eq24590 X0
       grind)
    | exact resolve eq24590 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24590
  have eq24772 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (σ x) x) (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq24688 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24688
    | (have j0 := eq24688 X0
       grind)
    | exact resolve eq24688 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24688
  have eq24838 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (σ x) x) (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) X0)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq24772
    | (have j0 := eq24772 X0
       grind)
    | exact resolve eq24772 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24772
  have eq24880 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (σ x) x) (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq24838 X0
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq24838
    | (have j0 := eq24838 X0
       grind)
    | exact resolve eq24838 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24838
  have eq24899 : ∀ X0 : G, (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (M.op (σ x) x) (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq24880 X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq24880
    | (have j0 := eq24880 X0
       grind)
    | exact resolve eq24880 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24880
  have eq24910 : ∀ X0 : G, (M.op (M.op (σ x) x) (M.op x y)) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) X0)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq24899
    | (have j0 := eq24899 X0
       grind)
    | exact resolve eq24899 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24899
  have eq34545 : ∀ X0 X1 X2 : G, (M.op (σ y) (σ y)) = (M.op (M.op (M.op (M.op (σ x) x) (M.op x y)) (M.op (M.op (σ y) X0) X1)) (M.op (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) X2)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | exact superpose eq24910 eq694
    | exact resolve eq694 eq24910
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq694 eq24910
  have eq34605 : ∀ X0 X1 X2 : G, (M.op (σ y) (σ y)) = (M.op (M.op (M.op (M.op (σ x) x) (M.op x y)) (M.op (M.op (σ y) X0) X1)) (M.op (M.op (M.op (σ y) x) (M.op x y)) X2)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq34545 X0 X1 X2
       have i₂ := eq254 sF3
       grind)
    | exact superpose eq254 eq34545
    | exact resolve eq34545 eq254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq254 eq34545
  have eq34669 : ∀ X2 : G, (M.op (σ y) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) x) (M.op x y)) (M.op (M.op (M.op (σ y) x) (M.op x y)) X2)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X2
    first
    | exact superpose eq18010 eq34605
    | exact resolve eq34605 eq18010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34605
  have eq34706 : (M.op (σ y) (σ y)) = (M.op (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) x)) x) (M.op x y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq18010 eq34669
    | exact resolve eq34669 eq18010
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18010 eq34669
  have eq34723 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq699 eq34706
    | exact resolve eq34706 eq699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq699 eq34706
  have eq34728 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq34723
       have r₂ := eq17052
       grind)
    | exact resolve eq34723 eq17052
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17052 eq34723
  have eq34735 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq34728 eq108
    | (have r₁ := eq108
       have r₂ := eq34728
       grind)
    | exact resolve eq108 eq34728
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq34728
  have eq34841 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq34735
  have eq34842 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq34841
  have eq34888 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12619 eq34842
    | exact resolve eq34842 eq12619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12619 eq34842
  have eq35000 : ∀ X0 : G, (σ y) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0)) (M.op (M.op (σ x) (σ y)) (M.op (σ y) X0))) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq34888 eq720
    | exact resolve eq720 eq34888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq720 eq34888
  have eq35031 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq1771 eq35000
    | exact resolve eq35000 eq1771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1771 eq35000
  have eq35044 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq35031 eq27
    | exact resolve eq27 eq35031
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35031
  have eq35073 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (σ x) ∨ x = y := by
    first
    | exact superpose eq14989 eq35044
    | (have r₁ := eq35044
       have r₂ := eq14989
       grind)
    | exact resolve eq35044 eq14989
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14989 eq35044
  have eq35074 : (σ (M.op x y)) = (σ x) ∨ x = y := by grind
  clear eq35073
  have eq35076 : x = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq35074 eq28
    | exact resolve eq28 eq35074
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq35074
  have eq35232 : x = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq30 eq35076
    | exact resolve eq35076 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq35076
  have eq35344 : x = y ∨ x = y ∨ x = y := by
    first
    | exact superpose eq35232 eq14827
    | exact resolve eq14827 eq35232
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14827 eq35232
  have eq35434 : x = y := by grind
  clear eq35344
  have eq35524 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq18
       have i₂ := eq35434
       grind)
    | exact superpose eq35434 eq18
    | exact resolve eq18 eq35434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq35525 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq35434
       grind)
    | exact superpose eq35434 eq24
    | exact resolve eq24 eq35434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq35434
  have eq35645 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq35525
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq35525
    | exact resolve eq35525 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq35525
  have eq35674 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq35645 eq26
    | exact resolve eq26 eq35645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq35645
  have eq36077 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq35674 eq118
    | exact resolve eq118 eq35674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq118 eq35674
  have eq36233 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq36077
       have i₂ := eq35524
       grind)
    | exact superpose eq35524 eq36077
    | exact resolve eq36077 eq35524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35524 eq36077
  have eq36264 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq36233 eq15
    | exact resolve eq15 eq36233
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36233
  have eq36310 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq36264
    | exact resolve eq36264 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq36264
  have eq36321 : False := by grind
  exact eq36321
