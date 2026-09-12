import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxx_pyx_pyx_pxx_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq43 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
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
       have r₂ := eq14 X0 (M.op X1 X0)
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X1 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq43 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq49 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq48 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq233 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq236 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq233 X0 X1
       have j1 := eq14 X0 X1
       grind)
    | (have r₁ := eq233 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | (have r₁ := eq233 X0 X0
       have r₂ := eq14 X0 X0
       grind)
    | (have r₁ := eq233 X0 X1
       have r₂ := eq14 X0 (M.op X1 X0)
       grind)
    | exact resolve eq233 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq233
  have eq3671 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    grind
  clear eq236
  have eq3754 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq3671 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3671
  have eq5648 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq3754 (σ X0) (σ X1)
       grind)
    | exact superpose eq3754 eq15
    | exact resolve eq15 eq3754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5661 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5648 X0 X1
       have i₂ := eq3754 X0 X1
       grind)
    | exact superpose eq3754 eq5648
    | exact resolve eq5648 eq3754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3754 eq5648
  have eq5673 : False := by grind
  exact eq5673

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pxy_pyx_pyx_pxy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
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
  clear eq25
  have eq75 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  clear eq23 eq37
  have eq90 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq75
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq75 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq90
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq90
    | exact resolve eq90 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq97 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq96
    | exact resolve eq96 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq97
    | exact resolve eq97 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq17765 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq98 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq98
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17766 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17765
    | exact resolve eq17765 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17765
  have eq17777 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17766
       have r₂ := eq28
       grind)
    | exact resolve eq17766 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17766
  have eq17779 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq17777
    | exact resolve eq17777 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17777
  have eq17782 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17779 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq17779
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq17779
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq17779
       grind)
    | exact resolve eq12 eq17779
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17779
  have eq17805 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq17782
  have eq17815 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17805
       have r₂ := eq27
       grind)
    | exact resolve eq17805 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17805
  have eq17827 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17815 eq98
    | exact resolve eq98 eq17815
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17815
  have eq17836 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq17827
  have eq17839 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq17836
       have r₂ := eq28
       grind)
    | exact resolve eq17836 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17836
  have eq17843 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq17839
  have eq17906 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq27 eq17843
    | exact resolve eq17843 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17843
  have eq17927 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) ∨ x = (M.op y y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq17906 eq98
    | exact resolve eq98 eq17906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq17906
  have eq17935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by grind
  clear eq17927
  have eq17937 : (M.op x y) = (M.op y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17935
       have r₂ := eq28
       grind)
    | exact resolve eq17935 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17935
  have eq17940 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k y x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq17937
       grind)
    | exact superpose eq17937 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq17937
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq17937
       grind)
    | exact resolve eq12 eq17937
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17937
  have eq17959 : (M.op x y) ≠ (M.op x y) ∨ x = (M.op y y) ∨ (M.op x y) = (k y x) := by grind
  clear eq17940
  have eq17966 : (M.op x y) = (k y x) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq17959
       have r₂ := eq19
       grind)
    | exact resolve eq17959 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17959
  have eq17976 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq75
       have i₂ := eq17966
       grind)
    | exact superpose eq17966 eq75
    | exact resolve eq75 eq17966
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17966
  have eq17996 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq21 eq17976
    | exact resolve eq17976 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17976
  have eq18011 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq17996 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq17996
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18016 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18011
    | exact resolve eq18011 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18011
  have eq18027 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq18016
       have r₂ := eq28
       grind)
    | exact resolve eq18016 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18016
  have eq18029 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq18027
    | exact resolve eq18027 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18027
  have eq20678 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq18029 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq18029
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq18029
       grind)
    | exact resolve eq12 eq18029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18029
  have eq20703 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq20678
  have eq20713 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq20703
       have r₂ := eq27
       grind)
    | exact resolve eq20703 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20703
  have eq20736 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20713 eq17996
    | exact resolve eq17996 eq20713
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20713
  have eq20739 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ (σ x) = (M.op (σ y) (σ y)) := by grind
  clear eq20736
  have eq20750 : (σ x) = (M.op (σ y) (σ y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq20739
       have r₂ := eq28
       grind)
    | exact resolve eq20739 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20739
  have eq20754 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq20750
  have eq20822 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op y y) := by
    first
    | exact superpose eq27 eq20754
    | exact resolve eq20754 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20754
  have eq20853 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20822 eq17996
    | exact resolve eq17996 eq20822
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17996 eq20822
  have eq20855 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op y y) := by grind
  clear eq20853
  have eq20865 : x = (M.op y y) := by
    first
    | (have r₁ := eq20855
       have r₂ := eq28
       grind)
    | exact resolve eq20855 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20855
  have eq20869 : (M.op x y) = (k y x) := by grind
  clear eq20865
  have eq20940 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq20869
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq20869
    | exact resolve eq20869 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq20869
  have eq20967 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq20940
       grind)
    | exact superpose eq20940 eq75
    | exact resolve eq75 eq20940
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq20940
  have eq20985 : (σ (M.op x y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq21 eq20967
    | exact resolve eq20967 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq20967
  have eq21004 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20985 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq20985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21005 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq21004
    | exact resolve eq21004 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21004
  have eq21016 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq21005
       have r₂ := eq28
       grind)
    | exact resolve eq21005 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21005
  have eq21018 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq27 eq21016
    | exact resolve eq21016 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21016
  have eq30793 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq21018 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq21018
       grind)
    | (have r₁ := eq12 (σ x) (σ y)
       have r₂ := eq21018
       grind)
    | exact resolve eq12 eq21018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21018
  have eq30827 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq30793
  have eq30841 : (σ x) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by
    first
    | (have r₁ := eq30827
       have r₂ := eq27
       grind)
    | exact resolve eq30827 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30827
  have eq30851 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20985 eq30841
    | exact resolve eq30841 eq20985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30841
  have eq30858 : (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have r₁ := eq30851
       have r₂ := eq28
       grind)
    | exact resolve eq30851 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30851
  have eq30863 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) := by grind
  clear eq30858
  have eq30957 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20985 eq30863
    | exact resolve eq30863 eq20985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20985 eq30863
  have eq30979 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq27 eq30957
    | exact resolve eq30957 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq30957
  have eq30991 : False := by grind
  exact eq30991

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_x_pxy_x_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X0) := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X0 X3
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq14 X2 X0 X2
       have i₂ := eq14 X0 X2 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op (M.op x y) X0) := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq82 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ y = (k y x) := by
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
  have eq83 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq106 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  clear eq22
  have eq107 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq111 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq107
       have i₂ := eq71 sF3
       grind)
    | exact superpose eq71 eq107
    | exact resolve eq107 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107
  have eq113 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq111
       have i₂ := eq71 y
       grind)
    | exact superpose eq71 eq111
    | exact resolve eq111 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq106
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq106
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq106 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq120 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq106
       grind)
    | exact superpose eq106 eq16
    | exact resolve eq16 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
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
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq121
    | exact resolve eq121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq123 : y = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq122
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq122
    | exact resolve eq122 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122
  have eq124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have i₁ := eq123
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq123
    | exact resolve eq123 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq123
  have eq140 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq143 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq140
       have i₂ := eq71 sF1
       grind)
    | exact superpose eq71 eq140
    | exact resolve eq140 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140
  have eq145 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq143
       have i₂ := eq71 sF0
       grind)
    | exact superpose eq71 eq143
    | exact resolve eq143 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq143
  have eq245 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1
       have i₂ := eq14 X1 x X0
       grind)
    | (have i₁ := eq53 x
       have i₂ := eq14 x x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq252 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) x
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0
       have i₂ := eq14 X0 sF2 x
       grind)
    | (have i₁ := eq54 x
       have i₂ := eq14 sF2 x x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq262 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq429 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X0 X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X0 x X1
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq430 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X0 X1) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq51
    | exact resolve eq51 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq475 : (M.op (M.op (σ x) (σ y)) x) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq54 eq245
    | exact resolve eq245 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq482 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op (M.op x y) (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op x X0)
       have i₂ := eq245 X0 (M.op x X0)
       grind)
    | (have i₁ := eq53 (M.op x y)
       have i₂ := eq245 X0 (M.op x y)
       grind)
    | exact superpose eq245 eq53
    | exact resolve eq53 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq492 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq482 X0
       have i₂ := eq14 x sF0 (M.op x X0)
       grind)
    | exact superpose eq14 eq482
    | exact resolve eq482 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq482
  have eq494 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq492 X0
       have i₂ := eq245 x sF0
       grind)
    | exact superpose eq245 eq492
    | exact resolve eq492 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq585 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (M.op x y) X0) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq430 (M.op X0 X1) x
       have i₂ := eq429 X0 X1
       grind)
    | (have i₁ := eq430 (M.op x y) X0
       have i₂ := eq429 X0 X1
       grind)
    | exact superpose eq429 eq430
    | exact resolve eq430 eq429
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) (σ x)) (σ x)) := by
    first
    | exact superpose eq475 eq430
    | exact resolve eq430 eq475
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq611 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq430 eq592
    | exact resolve eq592 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq616 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq430 eq585
    | exact resolve eq585 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq1694 : (σ (M.op (k x x) (k x x))) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq78 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq78
    | exact resolve eq78 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43 eq78
  have eq1742 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op (k x x) (k x x))) := by
    first
    | (have i₁ := eq1694
       have i₂ := eq71 sF2
       grind)
    | exact superpose eq71 eq1694
    | exact resolve eq1694 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1694
  have eq1745 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq1742
       have i₂ := eq71 x
       grind)
    | exact superpose eq71 eq1742
    | exact resolve eq1742 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq1742
  have eq1747 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op (M.op x y) (M.op x x))) := by
    first
    | (have i₁ := eq1745
       have i₂ := eq245 x (M.op x x)
       grind)
    | exact superpose eq245 eq1745
    | exact resolve eq1745 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245 eq1745
  have eq1749 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq494 eq1747
    | exact resolve eq1747 eq494
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq494 eq1747
  have eq1751 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq255 eq1749
    | exact resolve eq1749 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq1749
  have eq1753 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq616 eq1751
    | exact resolve eq1751 eq616
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616 eq1751
  have eq1754 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq145 eq1753
    | exact resolve eq1753 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq1753
  have eq1767 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq1754 eq430
    | exact resolve eq430 eq1754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1771 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq430 eq1767
    | exact resolve eq1767 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1767
  have eq1779 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq611 eq1771
    | exact resolve eq1771 eq611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq611 eq1771
  have eq1785 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1754 eq1779
    | exact resolve eq1779 eq1754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1779
  have eq2793 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq262 X0 X1
       have i₂ := eq252 X0 X1
       grind)
    | exact superpose eq252 eq262
    | exact resolve eq262 eq252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq252 eq262
  have eq2799 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq1754 eq2793
    | exact resolve eq2793 eq1754
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1754 eq2793
  have eq5392 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = (M.op (M.op X0 X1) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2799 X1
       have i₂ := eq14 sF1 X1 x
       grind)
    | (have i₁ := eq2799 X0
       have i₂ := eq14 X0 sF1 sF1
       grind)
    | exact superpose eq14 eq2799
    | exact resolve eq2799 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2799
  have eq43934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq124 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43935 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq43934
    | exact resolve eq43934 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43934
  have eq43946 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq43935
       have r₂ := eq27
       grind)
    | exact resolve eq43935 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43935
  have eq43950 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq43946
    | exact resolve eq43946 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43946
  have eq43952 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq43950
    | exact resolve eq43950 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43950
  have eq43958 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq43952 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq43952
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq43952
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq43952
       grind)
    | exact resolve eq13 eq43952
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43952
  have eq44061 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq43958
       have r₂ := eq26
       grind)
    | exact resolve eq43958 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43958
  have eq44099 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq44061 eq124
    | exact resolve eq124 eq44061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44061
  have eq44107 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq44099
  have eq44109 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq44107
       have r₂ := eq27
       grind)
    | exact resolve eq44107 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44107
  have eq44485 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq44109
       grind)
    | exact superpose eq44109 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq44109
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq44109
       grind)
    | exact resolve eq13 eq44109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44563 : (M.op x y) = (k y x) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq44485
       have r₂ := eq18
       grind)
    | exact resolve eq44485 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44485
  have eq44582 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq106
       have i₂ := eq44563
       grind)
    | exact superpose eq44563 eq106
    | exact resolve eq106 eq44563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44563
  have eq44596 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq44582
    | exact resolve eq44582 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44582
  have eq44632 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44596 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq44596
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44635 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq44632
    | exact resolve eq44632 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44632
  have eq44646 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq44635
       have r₂ := eq27
       grind)
    | exact resolve eq44635 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44635
  have eq44650 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq44646
    | exact resolve eq44646 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44646
  have eq44651 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq44650
  have eq44654 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq44651
    | exact resolve eq44651 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44651
  have eq45054 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq44654 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq44654
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq44654
       grind)
    | exact resolve eq13 eq44654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44654
  have eq45157 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq45054
       have r₂ := eq26
       grind)
    | exact resolve eq45054 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45054
  have eq45203 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq45157 eq44596
    | exact resolve eq44596 eq45157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44596 eq45157
  have eq45205 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq45203
  have eq45209 : (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq45205
       have r₂ := eq27
       grind)
    | exact resolve eq45205 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45205
  have eq45213 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq45209 eq27
    | exact resolve eq27 eq45209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45214 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq45209 eq83
    | (have r₁ := eq83
       have r₂ := eq45209
       grind)
    | exact resolve eq83 eq45209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq83
  have eq45274 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq45214
  have eq53814 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq45274 eq124
    | exact resolve eq124 eq45274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53829 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq53814
  have eq53842 : (σ y) = (M.op (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq53829
       have r₂ := eq45213
       grind)
    | exact resolve eq53829 eq45213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53829
  have eq56356 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq53842 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq53842
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq53842
       grind)
    | exact resolve eq13 eq53842
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53842
  have eq56441 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq56356
    | exact resolve eq56356 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56356
  have eq56448 : (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq56441
       have r₂ := eq44109
       grind)
    | exact resolve eq56441 eq44109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44109 eq56441
  have eq56897 : (τ (σ y)) = (k y x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq56448 eq120
    | exact resolve eq120 eq56448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq120
  have eq56898 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq56448 eq124
    | exact resolve eq124 eq56448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq56448
  have eq56913 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ (M.op x y) = (M.op y x) := by grind
  clear eq56898
  have eq56926 : (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq56913
       have r₂ := eq45213
       grind)
    | exact resolve eq56913 eq45213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56913
  have eq56927 : y = (k y x) ∨ (M.op x y) = (M.op y x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq56897
    | exact resolve eq56897 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq56897
  have eq56934 : y = (k y x) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq56927
       have r₂ := eq82
       grind)
    | exact resolve eq56927 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82 eq56927
  have eq56939 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq56926
       grind)
    | exact superpose eq56926 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq56926
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq56926
       grind)
    | exact resolve eq13 eq56926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56926
  have eq57018 : (M.op x y) = (k y x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq56939
       have r₂ := eq18
       grind)
    | exact resolve eq56939 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56939
  have eq57037 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq106
       have i₂ := eq57018
       grind)
    | exact superpose eq57018 eq106
    | exact resolve eq106 eq57018
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57018
  have eq57051 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq57037
    | exact resolve eq57037 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57037
  have eq57091 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq57051 eq45274
    | exact resolve eq45274 eq57051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45274
  have eq57095 : (σ (M.op x y)) = (σ y) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by grind
  clear eq57091
  have eq57103 : (σ y) = (M.op (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq57095
       have r₂ := eq45213
       grind)
    | exact resolve eq57095 eq45213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57095
  have eq57152 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq57103 eq13
    | exact resolve eq13 eq57103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57103
  have eq57237 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq26 eq57152
    | exact resolve eq57152 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57152
  have eq57244 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq57237
       have r₂ := eq45209
       grind)
    | exact resolve eq57237 eq45209
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45209 eq57237
  have eq57265 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) := by
    first
    | exact superpose eq57244 eq57051
    | exact resolve eq57051 eq57244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57051 eq57244
  have eq57268 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq57265
  have eq57280 : y = (M.op x y) := by
    first
    | (have r₁ := eq57268
       have r₂ := eq45213
       grind)
    | exact resolve eq57268 eq45213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45213 eq57268
  have eq57710 : (σ y) = (σ (M.op x y)) := by
    first
    | exact superpose eq57280 eq20
    | exact resolve eq20 eq57280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq57798 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (σ (M.op x y))) = (M.op (M.op y y) X0) := by
    intro X0 X1
    first
    | exact superpose eq57280 eq5392
    | exact resolve eq5392 eq57280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5392
  have eq57888 : (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq57710
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq57710
    | exact resolve eq57710 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57710
  have eq57909 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ (M.op x y))) := by
    first
    | exact superpose eq57888 eq26
    | exact resolve eq26 eq57888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq58129 : (M.op (σ x) (σ y)) ≠ (M.op (σ (M.op x y)) (σ x)) ∨ (M.op (σ (M.op x y)) (σ x)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq57909 eq13
    | (have j0 := eq13 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq13 eq57909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61329 : y = (k y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq57280 eq56934
    | exact resolve eq56934 eq57280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56934
  have eq61333 : (σ y) = (k (σ y) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq106
       have i₂ := eq61329
       grind)
    | exact superpose eq61329 eq106
    | exact resolve eq106 eq61329
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61329
  have eq61356 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq57888 eq61333
    | exact resolve eq61333 eq57888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61333
  have eq61364 : (σ y) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
    first
    | (have i₁ := eq61356
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq61356
    | exact resolve eq61356 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61356
  have eq61371 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq57888 eq61364
    | exact resolve eq61364 eq57888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61364
  have eq61584 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq61371 eq11
    | (have j0 := eq11 (σ (M.op x y)) (σ x)
       grind)
    | exact resolve eq11 eq61371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq61585 : (σ (M.op x y)) = (M.op (σ x) (σ (M.op x y))) ∨ (M.op (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by grind
  clear eq61584
  have eq61587 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | exact superpose eq57909 eq61585
    | exact resolve eq61585 eq57909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61585
  have eq61596 : (M.op (σ (M.op x y)) (σ x)) = (M.op (σ x) (σ (M.op x y))) ∨ y = (M.op y x) := by
    first
    | (have r₁ := eq61587
       have r₂ := eq27
       grind)
    | exact resolve eq61587 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61587
  have eq61605 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq57909 eq61596
    | exact resolve eq61596 eq57909
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61596
  have eq103789 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by
    first
    | exact superpose eq61605 eq58129
    | (have r₁ := eq58129
       have r₂ := eq61605
       grind)
    | exact resolve eq58129 eq61605
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58129 eq61605
  have eq103790 : (M.op (σ x) (σ y)) = (k (σ (M.op x y)) (σ x)) ∨ y = (M.op y x) := by grind
  clear eq103789
  have eq103800 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ y = (M.op y x) := by
    first
    | exact superpose eq103790 eq61371
    | exact resolve eq61371 eq103790
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61371 eq103790
  have eq103802 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq103800
  have eq103804 : y = (M.op y x) := by
    first
    | (have r₁ := eq103802
       have r₂ := eq27
       grind)
    | exact resolve eq103802 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103802
  have eq103871 : y ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq103804
       grind)
    | exact superpose eq103804 eq13
    | exact resolve eq13 eq103804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103883 : (M.op y x) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq429 y x
       have i₂ := eq103804
       grind)
    | exact superpose eq103804 eq429
    | exact resolve eq429 eq103804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq429
  have eq104001 : (M.op y x) = (M.op y y) := by
    first
    | exact superpose eq57280 eq103883
    | exact resolve eq103883 eq57280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103883
  have eq104008 : y ≠ (M.op x y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq103871
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq103871
    | exact resolve eq103871 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq103871
  have eq104057 : y = (M.op y y) := by
    first
    | (have i₁ := eq104001
       have i₂ := eq103804
       grind)
    | exact superpose eq103804 eq104001
    | exact resolve eq104001 eq103804
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103804 eq104001
  have eq104061 : y = (k y x) := by
    first
    | (have r₁ := eq104008
       have r₂ := eq57280
       grind)
    | exact resolve eq104008 eq57280
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57280 eq104008
  have eq104148 : (σ y) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq113
       have i₂ := eq104057
       grind)
    | exact superpose eq104057 eq113
    | exact resolve eq113 eq104057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq104496 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq57888 eq104148
    | exact resolve eq104148 eq57888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104148
  have eq104580 : (σ y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq104496
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq104496
    | exact resolve eq104496 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104496
  have eq104626 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq57888 eq104580
    | exact resolve eq104580 eq57888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104580
  have eq104671 : (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq106
       have i₂ := eq104061
       grind)
    | exact superpose eq104061 eq106
    | exact resolve eq106 eq104061
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq104061
  have eq104694 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq57888 eq104671
    | exact resolve eq104671 eq57888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104671
  have eq104702 : (σ y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | (have i₁ := eq104694
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq104694
    | exact resolve eq104694 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq104694
  have eq104709 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq57888 eq104702
    | exact resolve eq104702 eq57888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57888 eq104702
  have eq104839 : (M.op (σ (M.op x y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq104626 eq430
    | exact resolve eq430 eq104626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430
  have eq104899 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op y y) (σ (M.op x y))) := by
    first
    | exact superpose eq104626 eq57798
    | exact resolve eq57798 eq104626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104928 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op y y) y) := by
    first
    | exact superpose eq57798 eq104899
    | exact resolve eq104899 eq57798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57798 eq104899
  have eq104970 : (M.op (σ (M.op x y)) (σ x)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1785 eq104839
    | exact resolve eq104839 eq1785
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1785 eq104839
  have eq105031 : (M.op y y) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq104928
       have i₂ := eq104057
       grind)
    | exact superpose eq104057 eq104928
    | exact resolve eq104928 eq104057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104928
  have eq105060 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq104626 eq104970
    | exact resolve eq104970 eq104626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104970
  have eq105105 : (σ (M.op x y)) = (M.op y y) := by
    first
    | exact superpose eq104626 eq105031
    | exact resolve eq105031 eq104626
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104626 eq105031
  have eq105158 : y = (σ (M.op x y)) := by
    first
    | (have i₁ := eq105105
       have i₂ := eq104057
       grind)
    | exact superpose eq104057 eq105105
    | exact resolve eq105105 eq104057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104057 eq105105
  have eq105310 : (M.op (σ x) (σ y)) = (M.op (σ x) y) := by
    first
    | exact superpose eq105158 eq57909
    | exact resolve eq57909 eq105158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57909
  have eq108150 : y = (k y (σ x)) := by
    first
    | exact superpose eq105158 eq104709
    | exact resolve eq104709 eq105158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104709
  have eq108164 : y = (M.op (σ x) y) ∨ y = (M.op (σ x) y) ∨ (M.op y (σ x)) = (M.op (σ x) y) := by
    first
    | exact superpose eq108150 eq11
    | (have j0 := eq11 y (σ x)
       grind)
    | exact resolve eq11 eq108150
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108150
  have eq108165 : y = (M.op (σ x) y) ∨ (M.op y (σ x)) = (M.op (σ x) y) := by grind
  clear eq108164
  have eq108191 : y = (M.op y (σ x)) := by
    first
    | exact superpose eq105158 eq105060
    | exact resolve eq105060 eq105158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105060
  have eq318696 : y = (M.op (σ x) (σ y)) ∨ (M.op y (σ x)) = (M.op (σ x) y) := by
    first
    | exact superpose eq105310 eq108165
    | exact resolve eq108165 eq105310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108165
  have eq318697 : (M.op (σ x) (σ y)) = (M.op y (σ x)) ∨ y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq105310 eq318696
    | exact resolve eq318696 eq105310
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105310 eq318696
  have eq318698 : y = (M.op (σ x) (σ y)) ∨ y = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq108191 eq318697
    | exact resolve eq318697 eq108191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108191 eq318697
  have eq318699 : y = (M.op (σ x) (σ y)) := by grind
  clear eq318698
  have eq318701 : y ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq318699 eq27
    | exact resolve eq27 eq318699
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq318699
  have eq319185 : False := by grind
  exact eq319185

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,Y) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyy_y_pxy_pyy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X0) := by
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
  have eq51 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 X0 X3
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq14 X2 X0 X2
       have i₂ := eq14 X0 X2 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op (M.op X0 X0) x) = (M.op (M.op x y) X0) := by
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
  have eq54 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq14
    | (have j0 := eq14 X0 (σ x) (σ y)
       grind)
    | exact resolve eq14 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq55 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X3 X3) (M.op X2 X2)) = (M.op (M.op (M.op X0 X1) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X3 (M.op X2 X2) X0
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq14 X0 (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq56 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X2 X2) (M.op X1 X3)) = (M.op (M.op (M.op X0 X0) X1) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq14 X2 (M.op X1 X3) X0
       have i₂ := eq14 X0 X1 X3
       grind)
    | (have i₁ := eq14 X0 (M.op X0 X0) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq14
    | exact resolve eq14 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq67 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) ≠ (M.op X0 (M.op X2 X2)) ∨ (M.op (M.op X0 X1) X2) = (k (M.op X2 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 X0) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | (have i₁ := eq13 (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ (M.op X0 (M.op X1 X2)) ∨ (M.op (M.op X0 X0) X1) = (k (M.op X1 X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 (M.op X0 X0) X1
       have i₂ := eq14 X0 X1 X2
       grind)
    | (have i₁ := eq13 (M.op X1 X2) X0
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq74 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq71 x
       grind)
    | exact superpose eq71 eq43
    | exact resolve eq43 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq75 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq71 sF2
       grind)
    | exact superpose eq71 eq49
    | exact resolve eq49 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
  have eq77 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq74
       have i₂ := eq71 sF2
       grind)
    | exact superpose eq71 eq74
    | exact resolve eq74 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
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
  have eq82 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
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
  have eq103 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq104 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq108 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq104
       have i₂ := eq71 sF3
       grind)
    | exact superpose eq71 eq104
    | exact resolve eq104 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq110 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq108
       have i₂ := eq71 y
       grind)
    | exact superpose eq71 eq108
    | exact resolve eq108 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108
  have eq136 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq139 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq136
       have i₂ := eq71 sF1
       grind)
    | exact superpose eq71 eq136
    | exact resolve eq136 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq141 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq139
       have i₂ := eq71 sF0
       grind)
    | exact superpose eq71 eq139
    | exact resolve eq139 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq146 : ∀ X0 : G, (σ (k X0 (M.op y y))) = (k (σ X0) (M.op (σ y) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq10 X0 (M.op y y)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq10
    | exact resolve eq10 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq240 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1
       have i₂ := eq14 X1 x X0
       grind)
    | (have i₁ := eq53 x
       have i₂ := eq14 x x x
       grind)
    | exact superpose eq14 eq53
    | exact resolve eq53 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq246 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = (M.op (M.op (M.op x y) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (M.op X0 X0) x
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq14
    | exact resolve eq14 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq249 : ∀ X0 X1 : G, (M.op (M.op (σ x) X0) X1) = (M.op (M.op (σ x) (σ y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq54 X0
       have i₂ := eq14 X0 sF2 x
       grind)
    | (have i₁ := eq54 x
       have i₂ := eq14 sF2 x x
       grind)
    | exact superpose eq14 eq54
    | exact resolve eq54 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq255 : ∀ X0 X1 : G, (M.op (M.op X1 X1) (M.op X0 X0)) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | exact superpose eq54 eq14
    | exact resolve eq14 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq271 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq34 X0 (τ X0)
       have i₂ := eq71 (τ X0)
       grind)
    | exact superpose eq71 eq34
    | exact resolve eq34 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34
  have eq282 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq271 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq271
    | exact resolve eq271 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq271
  have eq284 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq282 X0
       have i₂ := eq71 X0
       grind)
    | exact superpose eq71 eq282
    | exact resolve eq282 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq282
  have eq412 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X2 X2) X4) X3) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq51 (M.op X2 X2) X0 X3 X4
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq51 (M.op X1 X2) X0 X2 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq416 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (M.op X0 X0) X2) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 (M.op X0 X0) x X1 X2
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq418 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq51 X2 X2 X0 X3
       have i₂ := eq14 X2 X0 X1
       grind)
    | (have i₁ := eq51 X1 X2 X0 X3
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq51
    | exact resolve eq51 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq422 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X0 X1) x) := by
    intro X0 X1
    first
    | (have i₁ := eq51 X0 X0 x X1
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq51
    | exact resolve eq51 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq423 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X0 X1) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq51
    | exact resolve eq51 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq468 : (M.op (M.op (σ x) (σ y)) x) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq54 eq240
    | exact resolve eq240 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq475 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op (M.op x y) (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op x X0)
       have i₂ := eq240 X0 (M.op x X0)
       grind)
    | (have i₁ := eq53 (M.op x y)
       have i₂ := eq240 X0 (M.op x y)
       grind)
    | exact superpose eq240 eq53
    | exact resolve eq53 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq486 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq475 X0
       have i₂ := eq14 x sF0 (M.op x X0)
       grind)
    | exact superpose eq14 eq475
    | exact resolve eq475 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq475
  have eq488 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq486 X0
       have i₂ := eq240 x sF0
       grind)
    | exact superpose eq240 eq486
    | exact resolve eq486 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq486
  have eq509 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (σ x) X0)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op (σ x) X0)) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq249 eq14
    | exact resolve eq14 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq536 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op (M.op X3 X4) X2) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq55 X3 X4 X2 X0
       have i₂ := eq51 X0 X0 (M.op X2 X2) X1
       grind)
    | (have i₁ := eq55 X3 X4 X2 X0
       have i₂ := eq51 X0 X1 (M.op X2 X2) X0
       grind)
    | exact superpose eq51 eq55
    | exact resolve eq55 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55
  have eq627 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op X4 X4) X2) X0) := by
    intro X0 X1 X2 X3 X4
    first
    | (have i₁ := eq56 X4 X2 X0 X3
       have i₂ := eq51 X0 X0 (M.op X2 X3) X1
       grind)
    | (have i₁ := eq56 X4 X2 X0 X3
       have i₂ := eq51 X0 X1 (M.op X2 X3) X0
       grind)
    | exact superpose eq51 eq56
    | exact resolve eq56 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq676 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X1) X2) ≠ (M.op (M.op X1 X3) (M.op X2 X2)) ∨ (M.op (M.op X1 X3) (M.op X2 X2)) = (k (M.op X1 X3) (M.op X2 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq13 (M.op X1 X3) (M.op X2 X2)
       have i₂ := eq56 X0 X1 X2 X3
       grind)
    | exact superpose eq56 eq13
    | (have j0 := eq13 (M.op X1 X3) (M.op X2 X2)
       grind)
    | exact resolve eq13 eq56
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq721 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op (M.op x y) X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq422 (M.op X0 X1) x
       have i₂ := eq422 X0 X1
       grind)
    | (have i₁ := eq422 (M.op x y) X0
       have i₂ := eq422 X0 X1
       grind)
    | exact superpose eq422 eq422
    | exact resolve eq422 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq762 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq721 sF0 X1
       have i₂ := eq14 sF0 x x
       grind)
    | (have i₁ := eq721 x X1
       have i₂ := eq14 x sF0 x
       grind)
    | exact superpose eq14 eq721
    | exact resolve eq721 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq721
  have eq776 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq762 X0 X1
       have i₂ := eq240 x sF0
       grind)
    | exact superpose eq240 eq762
    | exact resolve eq762 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq762
  have eq797 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (M.op x y) X0) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq423 (M.op X0 X1) x
       have i₂ := eq422 X0 X1
       grind)
    | (have i₁ := eq423 (M.op x y) X0
       have i₂ := eq422 X0 X1
       grind)
    | exact superpose eq422 eq423
    | exact resolve eq423 eq422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq422
  have eq806 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) (σ x)) (σ x)) := by
    first
    | exact superpose eq468 eq423
    | exact resolve eq423 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468
  have eq836 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq423 eq806
    | exact resolve eq806 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806
  have eq843 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq423 eq797
    | exact resolve eq797 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq797
  have eq1068 : ∀ X0 : G, (M.op (M.op x y) X0) ≠ (M.op X0 (M.op x x)) ∨ (M.op (M.op x y) X0) = (k (M.op x x) X0) := by
    intro X0
    first
    | (have i₁ := eq67 X0 X0 x
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq67
    | exact resolve eq67 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67
  have eq1119 : ∀ X0 X1 : G, (M.op (M.op x y) X0) ≠ (M.op X0 (M.op x X1)) ∨ (M.op (M.op x y) X0) = (k (M.op x X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X0 x x
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq68
    | (have r₁ := eq68 (M.op x y) x y
       have r₂ := eq53 (M.op x y)
       grind)
    | exact resolve eq68 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq1144 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) ≠ (M.op (M.op (M.op X2 X3) (M.op X2 X3)) X0) ∨ (M.op (M.op (M.op X2 X3) (M.op X2 X3)) X0) = (k (M.op X0 X1) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq68 (M.op X2 X3) X0 X1
       have i₂ := eq14 (M.op X0 X1) X2 X3
       grind)
    | (have i₁ := eq68 (M.op X0 X0) X1 X2
       have i₂ := eq14 X0 (M.op X1 X2) X2
       grind)
    | exact superpose eq14 eq68
    | (have j0 := eq68 (M.op X2 X3) X0 X1
       grind)
    | (have r₁ := eq68 (M.op X1 X2) X1 X2
       have r₂ := eq14 (M.op X1 X2) X1 X2
       grind)
    | (have r₁ := eq68 (M.op X0 X0) X0 X0
       have r₂ := eq14 X0 (M.op X0 X0) (M.op X0 X0)
       grind)
    | exact resolve eq68 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq1412 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq82 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq82 X0 X1
       grind)
    | exact superpose eq82 eq13
    | (have j1 := eq82 X1 X0
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq82 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq82 X0 X1
       grind)
    | exact resolve eq13 eq82
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq82
  have eq1428 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (k (σ X1) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1412 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1412
  have eq1434 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1428 X0 X1
       have i₂ := eq10 X1 X0
       grind)
    | exact superpose eq10 eq1428
    | (have j0 := eq1428 X0 X1
       grind)
    | exact resolve eq1428 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1428
  have eq1435 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq1434 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1434
  have eq1630 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ X0)) = (M.op (σ (M.op X0 X0)) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq54 (σ X0)
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq54
    | exact resolve eq54 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq1776 : (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) = (σ (M.op (k x x) (k x x))) := by
    first
    | exact superpose eq49 eq284
    | exact resolve eq284 eq49
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq1798 : (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq1776
       have i₂ := eq71 x
       grind)
    | exact superpose eq71 eq1776
    | exact resolve eq1776 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1776
  have eq1800 : (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) = (σ (M.op (M.op x y) (M.op x x))) := by
    first
    | (have i₁ := eq1798
       have i₂ := eq240 x (M.op x x)
       grind)
    | exact superpose eq240 eq1798
    | exact resolve eq1798 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1798
  have eq1802 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq488 eq1800
    | exact resolve eq1800 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1800
  have eq1804 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq1802
       have i₂ := eq71 sF2
       grind)
    | exact superpose eq71 eq1802
    | exact resolve eq1802 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1802
  have eq1806 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq249 eq1804
    | exact resolve eq1804 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq1804
  have eq1808 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq843 eq1806
    | exact resolve eq1806 eq843
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843 eq1806
  have eq1809 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq141 eq1808
    | exact resolve eq1808 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq141 eq1808
  have eq1812 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq1809 eq14
    | exact resolve eq14 eq1809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1820 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (σ x)) := by
    first
    | exact superpose eq1809 eq423
    | exact resolve eq423 eq1809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1824 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq423 eq1820
    | exact resolve eq1820 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1820
  have eq1830 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq836 eq1824
    | exact resolve eq1824 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1824
  have eq1835 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    first
    | exact superpose eq1809 eq1830
    | exact resolve eq1830 eq1809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1830
  have eq2427 : ∀ X0 : G, (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) (M.op X0 X0)) = (M.op (M.op (M.op x y) X0) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq836 eq246
    | exact resolve eq246 eq836
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq836
  have eq2551 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) (M.op X0 X0)) := by
    intro X0
    first
    | exact superpose eq1809 eq2427
    | exact resolve eq2427 eq1809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2427
  have eq2570 : ∀ X0 : G, (M.op (M.op (M.op x y) X0) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) X0) (σ (M.op x y))) := by
    intro X0
    first
    | (have i₁ := eq2551 X0
       have i₂ := eq246 X0 sF1
       grind)
    | exact superpose eq246 eq2551
    | exact resolve eq2551 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2551
  have eq2619 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq255 X0 X1
       have i₂ := eq246 X0 X1
       grind)
    | exact superpose eq246 eq255
    | exact resolve eq255 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq255
  have eq2747 : ∀ X0 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0
    first
    | exact superpose eq1809 eq2619
    | exact resolve eq2619 eq1809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1809
  have eq2751 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2619 X1 X2
       have i₂ := eq418 sF4 X1 X2 x
       grind)
    | (have i₁ := eq2619 x X0
       have i₂ := eq418 X0 X1 sF4 x
       grind)
    | exact superpose eq418 eq2619
    | exact resolve eq2619 eq418
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3285 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ (M.op x X0))) = (M.op (σ (M.op (M.op x y) (M.op x X0))) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq1630 (M.op x X0)
       have i₂ := eq240 X0 (M.op x X0)
       grind)
    | (have i₁ := eq1630 (M.op x y)
       have i₂ := eq240 X0 (M.op x y)
       grind)
    | exact superpose eq240 eq1630
    | exact resolve eq1630 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3329 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ (M.op x X0))) = (M.op (σ (M.op (M.op x y) (M.op x y))) (σ x)) := by
    intro X0
    first
    | exact superpose eq488 eq3285
    | exact resolve eq3285 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3285
  have eq3342 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ (M.op x X0))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq1630 eq3329
    | exact resolve eq3329 eq1630
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1630 eq3329
  have eq3348 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq20 eq3342
    | (have j0 := eq3342 X0
       grind)
    | exact resolve eq3342 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3342
  have eq3350 : ∀ X0 : G, (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ (M.op x X0))) := by
    intro X0
    first
    | exact superpose eq1835 eq3348
    | exact resolve eq3348 eq1835
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1835 eq3348
  have eq3484 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op x y)) = (M.op (M.op X0 X2) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2751 X1 X1 sF0
       have i₂ := eq14 sF0 X1 X2
       grind)
    | (have i₁ := eq2751 X0 X1 X2
       have i₂ := eq14 X0 sF0 X2
       grind)
    | exact superpose eq14 eq2751
    | exact resolve eq2751 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5946 : ∀ X0 X1 : G, (M.op (M.op X0 X0) (M.op (σ x) (σ y))) = (M.op (M.op X0 X1) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq1812 X1
       have i₂ := eq14 sF1 X1 x
       grind)
    | (have i₁ := eq1812 X0
       have i₂ := eq14 X0 sF1 sF1
       grind)
    | exact superpose eq14 eq1812
    | exact resolve eq1812 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1812
  have eq7469 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = (M.op (M.op X0 X1) (σ (M.op x y))) := by
    intro X0 X1
    first
    | (have i₁ := eq2747 X1
       have i₂ := eq14 sF1 X1 x
       grind)
    | (have i₁ := eq2747 X0
       have i₂ := eq14 X0 sF1 sF1
       grind)
    | exact superpose eq14 eq2747
    | exact resolve eq2747 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2747
  have eq8568 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op x y) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq412 X0 X1 X2 X3 x
       have i₂ := eq416 X2 X3 x
       grind)
    | exact superpose eq416 eq412
    | exact resolve eq412 eq416
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq412 eq416
  have eq9592 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op (M.op x y) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq536 X0 X1 X2 x x
       have i₂ := eq8568 x x X2 X0
       grind)
    | (have i₁ := eq536 x X1 X2 x y
       have i₂ := eq8568 X0 X1 X2 x
       grind)
    | exact superpose eq8568 eq536
    | (have j0 := eq536 X0 X1 X2 x y
       grind)
    | exact resolve eq536 eq8568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq536
  have eq13158 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op x y) X2) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq627 X0 X1 X2 X3 x
       have i₂ := eq8568 x x X2 X0
       grind)
    | exact superpose eq8568 eq627
    | exact resolve eq627 eq8568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq19518 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) ≠ (M.op (M.op x y) (M.op x x)) ∨ (M.op (M.op x y) (M.op x X0)) = (k (M.op x x) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq1068 (M.op x X0)
       have i₂ := eq240 X0 (M.op x x)
       grind)
    | (have i₁ := eq1068 (M.op x y)
       have i₂ := eq240 X0 (M.op x x)
       grind)
    | exact superpose eq240 eq1068
    | (have j0 := eq1068 (M.op x X0)
       grind)
    | (have r₁ := eq1068 (M.op x x)
       have r₂ := eq240 x (M.op x x)
       grind)
    | exact resolve eq1068 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1068
  have eq19549 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) ≠ (M.op (M.op x y) (M.op x X0)) ∨ (M.op (M.op x y) (M.op x X0)) = (k (M.op x x) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq488 eq19518
    | (have j0 := eq19518 X0
       grind)
    | (have r₁ := eq19518 y
       have r₂ := eq488 x
       grind)
    | exact resolve eq19518 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19518
  have eq19582 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (k (M.op x x) (M.op x X0)) := by
    intro X0
    first
    | (have j0 := eq19549 X0
       grind)
    | (have r₁ := eq19549 X0
       have r₂ := eq488 X0
       grind)
    | (have r₁ := eq19549 y
       have r₂ := eq488 y
       grind)
    | exact resolve eq19549 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19549
  have eq19615 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (k (M.op x x) (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq488 eq19582
    | exact resolve eq19582 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19582
  have eq19996 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x X0)) ≠ (M.op (M.op x y) (M.op x X1)) ∨ (M.op (M.op x y) (M.op x X1)) = (k (M.op x X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1119 (M.op x X1) X0
       have i₂ := eq240 X1 (M.op x X0)
       grind)
    | (have i₁ := eq1119 (M.op x y) X1
       have i₂ := eq240 X0 (M.op x X1)
       grind)
    | exact superpose eq240 eq1119
    | (have j0 := eq1119 (M.op x X1) X0
       grind)
    | (have r₁ := eq1119 (M.op x y) y
       have r₂ := eq240 y (M.op x y)
       grind)
    | (have r₁ := eq1119 (M.op x X0) X0
       have r₂ := eq240 X0 (M.op x X0)
       grind)
    | exact resolve eq1119 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1119
  have eq20027 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) ≠ (M.op (M.op x y) (M.op x X0)) ∨ (M.op (M.op x y) (M.op x X1)) = (k (M.op x X0) (M.op x X1)) := by
    intro X0 X1
    first
    | exact superpose eq488 eq19996
    | (have j0 := eq19996 y X0
       grind)
    | (have r₁ := eq19996 y X0
       have r₂ := eq488 X0
       grind)
    | (have r₁ := eq19996 X0 y
       have r₂ := eq488 X0
       grind)
    | exact resolve eq19996 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19996
  have eq20060 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x X1)) = (k (M.op x X0) (M.op x X1)) := by
    intro X0 X1
    first
    | (have j0 := eq20027 X0 X1
       grind)
    | (have r₁ := eq20027 X0 X1
       have r₂ := eq488 X0
       grind)
    | (have r₁ := eq20027 y X1
       have r₂ := eq488 y
       grind)
    | exact resolve eq20027 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20027
  have eq20093 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (k (M.op x X0) (M.op x X1)) := by
    intro X0 X1
    first
    | exact superpose eq488 eq20060
    | exact resolve eq20060 eq488
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq488 eq20060
  have eq20449 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) ∨ (σ X0) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq1435 X0 X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq1435
    | (have j0 := eq1435 X0 X1
       grind)
    | exact resolve eq1435 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq1435
  have eq20534 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20449 (τ X0) X1
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq20449
    | exact resolve eq20449 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq20593 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (σ (M.op x x)) := by
    intro X0
    first
    | (have i₁ := eq20449 x X0
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq20449
    | (have j0 := eq20449 x X0
       grind)
    | exact resolve eq20449 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20449
  have eq20803 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    intro X0
    first
    | (have i₁ := eq20593 X0
       have i₂ := eq77
       grind)
    | exact superpose eq77 eq20593
    | (have j0 := eq20593 X0
       grind)
    | exact resolve eq20593 eq77
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20593
  have eq20808 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (σ (M.op (τ X0) (τ X0))) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20534 X0 X1
       have i₂ := eq38 X0 X1
       grind)
    | exact superpose eq38 eq20534
    | (have j0 := eq20534 X0 X1
       grind)
    | exact resolve eq20534 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38 eq20534
  have eq20847 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op X0 (σ X1)) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq20808 X0 X1
       have i₂ := eq284 X0
       grind)
    | exact superpose eq284 eq20808
    | (have j0 := eq20808 X0 X1
       grind)
    | exact resolve eq20808 eq284
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284 eq20808
  have eq41783 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X0) X1) X2) ≠ (M.op (M.op (M.op x y) X2) X1) ∨ (M.op (M.op X1 X3) (M.op X2 X2)) = (k (M.op X1 X3) (M.op X2 X2)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq676 X0 X1 X2 X3
       have i₂ := eq9592 X1 X3 X2
       grind)
    | exact superpose eq9592 eq676
    | (have j0 := eq676 X0 X1 X2 X3
       grind)
    | (have r₁ := eq676 (M.op X2 X2) (M.op x y) (M.op X2 X2) X2
       have r₂ := eq9592 (M.op (M.op X2 X2) (M.op X2 X2)) (M.op x y) X2
       grind)
    | exact resolve eq676 eq9592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq676
  have eq41784 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op x y) X2) X1) ≠ (M.op (M.op (M.op x y) X1) X2) ∨ (M.op (M.op X1 X3) (M.op X2 X2)) = (k (M.op X1 X3) (M.op X2 X2)) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq41783 x X1 X2 X3
       have i₂ := eq8568 x x X1 X2
       grind)
    | exact superpose eq8568 eq41783
    | (have j0 := eq41783 x X1 X2 X3
       grind)
    | (have r₁ := eq41783 X1 X2 X2 X3
       have r₂ := eq8568 X1 X1 X2 X2
       grind)
    | exact resolve eq41783 eq8568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41783
  have eq41785 : ∀ X1 X2 X3 : G, (M.op (M.op (M.op x y) X2) X1) ≠ (M.op (M.op (M.op x y) X1) X2) ∨ (k (M.op X1 X3) (M.op X2 X2)) = (M.op (M.op (M.op x y) X2) X1) := by
    intro X1 X2 X3
    first
    | (have i₁ := eq41784 X1 X2 X3
       have i₂ := eq9592 X1 X3 X2
       grind)
    | exact superpose eq9592 eq41784
    | (have j0 := eq41784 X1 X2 X3
       grind)
    | exact resolve eq41784 eq9592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41784
  have eq41912 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) X0) = (k (M.op X0 X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have j0 := eq41785 X0 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41785
  have eq44093 : (σ (k (M.op y y) (M.op y y))) = (k (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq146 (M.op y y)
       have i₂ := eq110
       grind)
    | exact superpose eq110 eq146
    | exact resolve eq146 eq110
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq110 eq146
  have eq44190 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (k (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq44093
       have i₂ := eq71 (M.op sF3 sF3)
       grind)
    | exact superpose eq71 eq44093
    | exact resolve eq44093 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44093
  have eq44196 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (M.op (M.op y y) (M.op y y))) := by
    first
    | (have i₁ := eq44190
       have i₂ := eq71 (M.op y y)
       grind)
    | exact superpose eq71 eq44190
    | exact resolve eq44190 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44190
  have eq44198 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (M.op (M.op (M.op x y) y) y)) := by
    first
    | (have i₁ := eq44196
       have i₂ := eq9592 y y y
       grind)
    | exact superpose eq9592 eq44196
    | exact resolve eq44196 eq9592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44196
  have eq44199 : (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) = (σ (M.op (M.op y y) (M.op x y))) := by
    first
    | (have i₁ := eq44198
       have i₂ := eq14 y sF0 y
       grind)
    | exact superpose eq14 eq44198
    | exact resolve eq44198 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44198
  have eq44200 : (σ (M.op (M.op y y) (M.op x y))) = (M.op (M.op (M.op x y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq44199
       have i₂ := eq9592 sF3 sF3 sF3
       grind)
    | exact superpose eq9592 eq44199
    | exact resolve eq44199 eq9592
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9592 eq44199
  have eq44202 : ∀ X0 : G, (M.op (M.op (M.op x y) (σ y)) (σ y)) = (σ (M.op (M.op y X0) (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq3484 eq44200
    | exact resolve eq44200 eq3484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3484 eq44200
  have eq58942 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) ≠ (M.op (M.op (M.op x y) (M.op X2 X3)) X0) ∨ (M.op (M.op (M.op X2 X3) (M.op X2 X3)) X0) = (k (M.op X0 X1) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq1144 X0 X1 X2 X3
       have i₂ := eq8568 X2 X3 (M.op X2 X3) X0
       grind)
    | (have i₁ := eq1144 X3 X1 x y
       have i₂ := eq8568 X0 X1 (M.op x y) X3
       grind)
    | exact superpose eq8568 eq1144
    | (have j0 := eq1144 X0 X1 X2 X3
       grind)
    | (have r₁ := eq1144 x y x y
       have r₂ := eq8568 x y (M.op x y) x
       grind)
    | exact resolve eq1144 eq8568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1144
  have eq58943 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) (M.op X0 X1)) X2) ≠ (M.op (M.op (M.op x y) (M.op x y)) X0) ∨ (M.op (M.op (M.op X2 X3) (M.op X2 X3)) X0) = (k (M.op X0 X1) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq776 eq58942
    | (have j0 := eq58942 X0 X1 X2 X3
       grind)
    | exact resolve eq58942 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58942
  have eq58944 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) ≠ (M.op (M.op (M.op x y) (M.op X0 X1)) X2) ∨ (M.op (M.op (M.op X2 X3) (M.op X2 X3)) X0) = (k (M.op X0 X1) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq58943 X0 X1 X2 X3
       have i₂ := eq8568 X0 X1 (M.op X0 X1) X2
       grind)
    | (have i₁ := eq58943 x y X3 X3
       have i₂ := eq8568 X0 X1 (M.op x y) X3
       grind)
    | exact superpose eq8568 eq58943
    | (have j0 := eq58943 X0 X1 X2 X3
       grind)
    | (have r₁ := eq58943 x y x X3
       have r₂ := eq8568 x y (M.op x y) x
       grind)
    | exact resolve eq58943 eq8568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58943
  have eq58945 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) ≠ (M.op (M.op (M.op x y) (M.op x y)) X2) ∨ (M.op (M.op (M.op X2 X3) (M.op X2 X3)) X0) = (k (M.op X0 X1) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq776 eq58944
    | (have j0 := eq58944 X0 X1 X2 X3
       grind)
    | exact resolve eq58944 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58944
  have eq58946 : ∀ X0 X1 X2 X3 : G, (k (M.op X0 X1) (M.op X2 X3)) = (M.op (M.op (M.op x y) (M.op X2 X3)) X0) ∨ (M.op (M.op (M.op x y) (M.op x y)) X0) ≠ (M.op (M.op (M.op x y) (M.op x y)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq58945 X0 X1 X2 X3
       have i₂ := eq8568 X2 X3 (M.op X2 X3) X0
       grind)
    | (have i₁ := eq58945 X3 X1 x y
       have i₂ := eq8568 X0 X1 (M.op x y) X3
       grind)
    | exact superpose eq8568 eq58945
    | (have j0 := eq58945 X0 X1 X2 X3
       grind)
    | (have r₁ := eq58945 X3 X1 X3 X3
       have r₂ := eq8568 x y (M.op x y) X3
       grind)
    | exact resolve eq58945 eq8568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8568 eq58945
  have eq58947 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) ≠ (M.op (M.op (M.op x y) (M.op x y)) X2) ∨ (M.op (M.op (M.op x y) (M.op x y)) X0) = (k (M.op X0 X1) (M.op X2 X3)) := by
    intro X0 X1 X2 X3
    first
    | exact superpose eq776 eq58946
    | (have j0 := eq58946 X0 X1 X2 X3
       grind)
    | exact resolve eq58946 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58946
  have eq59014 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) (M.op x y)) X0) = (k (M.op X0 X1) (M.op X0 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq58947 X0 X1 X0 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq58947
  have eq98336 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq20803 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq20803
    | (have j0 := eq20803 y
       grind)
    | exact resolve eq20803 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq20803
  have eq98481 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq98336
       have i₂ := eq103
       grind)
    | exact superpose eq103 eq98336
    | exact resolve eq98336 eq103
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98336
  have eq98525 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq26 eq98481
    | exact resolve eq98481 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98481
  have eq98613 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq20847 X0 (τ X0)
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq20847
    | (have j0 := eq20847 X1 X1
       grind)
    | exact resolve eq20847 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20847
  have eq99182 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq103
       have i₂ := eq98613 y x
       grind)
    | exact superpose eq98613 eq103
    | (have j1 := eq98613 x x
       grind)
    | exact resolve eq103 eq98613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103 eq98613
  have eq99382 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq99182
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq99182
    | exact resolve eq99182 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99182
  have eq99552 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq99382
    | exact resolve eq99382 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99382
  have eq99657 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq99552 eq98525
    | exact resolve eq98525 eq99552
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98525 eq99552
  have eq99664 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq99657
       have r₂ := eq27
       grind)
    | exact resolve eq99657 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99657
  have eq99782 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq99664 eq76
    | exact resolve eq76 eq99664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76 eq99664
  have eq100052 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq99782
    | exact resolve eq99782 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq99782
  have eq100053 : x = (M.op x x) := by grind
  clear eq100052
  have eq100115 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq77
       have i₂ := eq100053
       grind)
    | exact superpose eq100053 eq77
    | exact resolve eq77 eq100053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq100137 : (k x x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq19615 x
       have i₂ := eq100053
       grind)
    | exact superpose eq100053 eq19615
    | exact resolve eq19615 eq100053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19615
  have eq100352 : (M.op x x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq100137
       have i₂ := eq71 x
       grind)
    | exact superpose eq71 eq100137
    | exact resolve eq100137 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100137
  have eq100363 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq100115
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq100115
    | exact resolve eq100115 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100115
  have eq100401 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq100352
       have i₂ := eq100053
       grind)
    | exact superpose eq100053 eq100352
    | exact resolve eq100352 eq100053
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100053 eq100352
  have eq100779 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq100363 eq423
    | exact resolve eq423 eq100363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq423
  have eq100873 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq100363 eq100779
    | exact resolve eq100779 eq100363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100779
  have eq101424 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (σ x) X0)) = (M.op (M.op (M.op x y) (M.op (σ x) X0)) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq2619 eq509
    | exact resolve eq509 eq2619
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509 eq2619
  have eq101425 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (M.op (σ x) X0)) = (M.op (M.op (M.op x y) (M.op x y)) X1) := by
    intro X0 X1 X2
    first
    | exact superpose eq776 eq101424
    | exact resolve eq101424 eq776
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq776 eq101424
  have eq101426 : ∀ X0 X1 X2 : G, (M.op x X1) = (M.op (M.op X1 X2) (M.op (σ x) X0)) := by
    intro X0 X1 X2
    first
    | exact superpose eq100401 eq101425
    | exact resolve eq101425 eq100401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101425
  have eq101427 : ∀ X1 : G, (M.op x X1) = (M.op (M.op (M.op x y) (σ x)) X1) := by
    intro X1
    first
    | (have i₁ := eq101426 x x X1
       have i₂ := eq13158 x X1 sF2 x
       grind)
    | (have i₁ := eq101426 x (M.op x y) x
       have i₂ := eq13158 (M.op sF2 x) X1 x x
       grind)
    | exact superpose eq13158 eq101426
    | exact resolve eq101426 eq13158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101426
  have eq101660 : ∀ X0 X1 : G, (M.op x X0) = (M.op (M.op X0 X1) (M.op (σ x) (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq2751 eq101427
    | exact resolve eq101427 eq2751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2751
  have eq101896 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) X1) = (M.op (M.op X1 X2) (M.op (M.op x y) (σ x))) := by
    intro X0 X1 X2
    first
    | exact superpose eq101427 eq418
    | exact resolve eq418 eq101427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq418
  have eq101961 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (σ x))) = (k (M.op (M.op (M.op x y) (σ x)) X1) (M.op x X0)) := by
    intro X0 X1
    first
    | exact superpose eq101427 eq59014
    | exact resolve eq59014 eq101427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59014
  have eq102012 : ∀ X0 X1 : G, (k (M.op x X1) (M.op x X0)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (M.op x y) (σ x))) := by
    intro X0 X1
    first
    | exact superpose eq101427 eq101961
    | exact resolve eq101961 eq101427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101427 eq101961
  have eq102047 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op (M.op x y) (M.op x y)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq101896 X0 X0 X1
       have i₂ := eq13158 X0 X1 sF0 sF2
       grind)
    | (have i₁ := eq101896 X0 (M.op x y) x
       have i₂ := eq13158 (M.op sF0 sF2) X1 x x
       grind)
    | exact superpose eq13158 eq101896
    | exact resolve eq101896 eq13158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101896
  have eq102204 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) = (k (M.op x X1) (M.op x X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq102012 X0 X1
       have i₂ := eq13158 sF0 sF0 sF0 sF2
       grind)
    | exact superpose eq13158 eq102012
    | exact resolve eq102012 eq13158
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13158 eq102012
  have eq102236 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op x X1) := by
    intro X0 X1
    first
    | exact superpose eq100401 eq102047
    | exact resolve eq102047 eq100401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102047
  have eq102337 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | (have i₁ := eq102204 x x
       have i₂ := eq20093 x x
       grind)
    | exact superpose eq20093 eq102204
    | exact resolve eq102204 eq20093
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20093 eq102204
  have eq102367 : ∀ X1 : G, (M.op (M.op x y) X1) = (M.op x X1) := by
    intro X1
    first
    | (have i₁ := eq102236 x X1
       have i₂ := eq240 x X1
       grind)
    | (have i₁ := eq102236 y X1
       have i₂ := eq240 x X1
       grind)
    | exact superpose eq240 eq102236
    | (have j0 := eq102236 y X1
       grind)
    | exact resolve eq102236 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102236
  have eq102437 : x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq100401 eq102337
    | exact resolve eq102337 eq100401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102337
  have eq102598 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq102437 eq3350
    | exact resolve eq3350 eq102437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3350
  have eq102718 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | (have i₁ := eq102598
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq102598
    | exact resolve eq102598 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq102598
  have eq102750 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq100873 eq102718
    | exact resolve eq102718 eq100873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100873 eq102718
  have eq103195 : (k (σ x) (σ x)) = (M.op (M.op (M.op x y) (σ (M.op x y))) (σ (M.op x y))) := by
    first
    | exact superpose eq102750 eq41912
    | exact resolve eq41912 eq102750
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41912 eq102750
  have eq103212 : (k (σ x) (σ x)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq5946 eq103195
    | exact resolve eq103195 eq5946
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5946 eq103195
  have eq103343 : (k (σ x) (σ x)) = (M.op (M.op (M.op x y) (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2570 eq103212
    | exact resolve eq103212 eq2570
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2570 eq103212
  have eq103419 : (k (σ x) (σ x)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x y)) := by
    first
    | exact superpose eq7469 eq103343
    | exact resolve eq103343 eq7469
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7469 eq103343
  have eq103458 : (k (σ x) (σ x)) = (M.op x (M.op x y)) := by
    first
    | exact superpose eq100401 eq103419
    | exact resolve eq103419 eq100401
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100401 eq103419
  have eq103485 : x = (k (σ x) (σ x)) := by
    first
    | exact superpose eq102437 eq103458
    | exact resolve eq103458 eq102437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102437 eq103458
  have eq103495 : x = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq103485
       have i₂ := eq71 sF2
       grind)
    | exact superpose eq71 eq103485
    | exact resolve eq103485 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq103485
  have eq103501 : x = (σ x) := by
    first
    | exact superpose eq100363 eq103495
    | exact resolve eq103495 eq100363
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100363 eq103495
  have eq103507 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq103501 eq26
    | exact resolve eq26 eq103501
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq103501
  have eq138105 : (σ (M.op x y)) = (M.op (M.op (M.op x y) (σ y)) (σ y)) := by
    first
    | exact superpose eq101660 eq44202
    | exact resolve eq44202 eq101660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44202 eq101660
  have eq138366 : (σ (M.op x y)) = (M.op (M.op x (σ y)) (σ y)) := by
    first
    | exact superpose eq102367 eq138105
    | exact resolve eq138105 eq102367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138105
  have eq138787 : (σ (M.op x y)) = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq138366
       have i₂ := eq240 sF3 sF3
       grind)
    | exact superpose eq240 eq138366
    | exact resolve eq138366 eq240
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq240 eq138366
  have eq139129 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq102367 eq138787
    | exact resolve eq138787 eq102367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102367 eq138787
  have eq139418 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq103507 eq139129
    | exact resolve eq139129 eq103507
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103507 eq139129
  have eq139657 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq139418
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq139418
    | exact resolve eq139418 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq139418
  have eq139810 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq139657
    | exact resolve eq139657 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq139657
  have eq139879 : False := by grind
  exact eq139879

/-- `Equation58`: `x = x ◇ (y ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = Y then m(Y,Y) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_y_pxx_pyy_pxy_Equation58 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) Law58 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law58.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X1 (M.op X2 X0))) = X0 := by
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
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (M.op X1 X0) X0 x
       have i₂ := eq9 X0 x X1
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq24 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq27 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq28 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq27
  have eq228 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq230 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = X1 ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq24 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq24
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq24 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq664 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq228 x y
       grind)
    | exact superpose eq228 eq16
    | (have j1 := eq228 x y
       grind)
    | exact resolve eq16 eq228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq673 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq228 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq2416 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq230 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq230
    | exact resolve eq230 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq230
  have eq2502 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq2416 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq2416
    | (have j0 := eq2416 X0 X1
       grind)
    | exact resolve eq2416 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2416
  have eq25290 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq664
       have i₂ := eq2502 x y
       grind)
    | exact superpose eq2502 eq664
    | (have j1 := eq2502 (σ x) (σ y)
       grind)
    | (have r₁ := eq664
       have r₂ := eq2502 x y
       grind)
    | (have r₁ := eq664
       have r₂ := eq2502 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq664
       have r₂ := eq2502 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq664 eq2502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq664
  have eq25291 : x = y ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq25290
  have eq25293 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25291
       grind)
    | exact superpose eq25291 eq16
    | exact resolve eq16 eq25291
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25291
  have eq25294 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq25293
       have r₂ := eq28 x
       grind)
    | exact resolve eq25293 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25293
  have eq25296 : y ≠ y ∨ x = y ∨ (k x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 x y
       have i₂ := eq25294
       grind)
    | exact superpose eq25294 eq13
    | (have j0 := eq13 x y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq25294
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq25294
       grind)
    | exact resolve eq13 eq25294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25299 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq19 y x
       have i₂ := eq25294
       grind)
    | exact superpose eq25294 eq19
    | exact resolve eq19 eq25294
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25294
  have eq25316 : (k x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq25296
  have eq25329 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq19 (σ y) (σ x)
       have i₂ := eq25299
       grind)
    | exact superpose eq25299 eq19
    | exact resolve eq19 eq25299
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq25299
  have eq25350 : (σ x) = (σ y) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq25329
       have i₂ := eq28 y
       grind)
    | exact superpose eq28 eq25329
    | exact resolve eq25329 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25329
  have eq25359 : y = (τ (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq25350
       grind)
    | exact superpose eq25350 eq10
    | exact resolve eq10 eq25350
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25350
  have eq25438 : x = y ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq25359
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq25359
    | exact resolve eq25359 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25359
  have eq25440 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq25438
       grind)
    | exact superpose eq25438 eq16
    | exact resolve eq16 eq25438
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25438
  have eq25441 : (σ y) = (σ (M.op y y)) ∨ y = (M.op y y) := by
    first
    | (have r₁ := eq25440
       have r₂ := eq28 x
       grind)
    | exact resolve eq25440 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25440
  have eq25464 : (M.op y y) = (τ (σ y)) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq25441
       grind)
    | exact superpose eq25441 eq10
    | exact resolve eq10 eq25441
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25441
  have eq25543 : y = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq25464
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq25464
    | exact resolve eq25464 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25464
  have eq25544 : y = (M.op y y) := by grind
  clear eq25543
  have eq265255 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq673 x y
       have i₂ := eq25316
       grind)
    | exact superpose eq25316 eq673
    | (have j0 := eq673 x y
       grind)
    | exact resolve eq673 eq25316
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673 eq25316
  have eq265328 : (σ y) ≠ (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq265255
  have eq265395 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq265328
       have i₂ := eq25544
       grind)
    | exact superpose eq25544 eq265328
    | exact resolve eq265328 eq25544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265328
  have eq265396 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq265395
  have eq265404 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq16
       have i₂ := eq265396
       grind)
    | exact superpose eq265396 eq16
    | exact resolve eq16 eq265396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq265450 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq13 (σ x) (σ y)
       have i₂ := eq265396
       grind)
    | exact superpose eq265396 eq13
    | (have j0 := eq13 (σ x) (σ y)
       grind)
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq265396
       grind)
    | exact resolve eq13 eq265396
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265396
  have eq265486 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq265450
  have eq265487 : (σ x) = (σ y) ∨ (k (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by grind
  clear eq265486
  have eq265496 : (σ (M.op y y)) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq265487
       have i₂ := eq28 y
       grind)
    | exact superpose eq28 eq265487
    | exact resolve eq265487 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265487
  have eq265513 : (σ (k x y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq265496
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq265496
    | exact resolve eq265496 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265496
  have eq265514 : (σ y) = (σ (k x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq265513
       have i₂ := eq25544
       grind)
    | exact superpose eq25544 eq265513
    | exact resolve eq265513 eq25544
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25544 eq265513
  have eq266283 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq2502 x y
       have i₂ := eq265514
       grind)
    | exact superpose eq265514 eq2502
    | (have j0 := eq2502 x y
       grind)
    | exact resolve eq2502 eq265514
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2502 eq265514
  have eq266407 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq266283
  have eq266454 : (σ x) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq266407
       have r₂ := eq265404
       grind)
    | exact resolve eq266407 eq265404
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266407
  have eq266729 : y = (τ (σ x)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq266454
       grind)
    | exact superpose eq266454 eq10
    | exact resolve eq10 eq266454
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266454
  have eq266907 : x = y ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq266729
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq266729
    | exact resolve eq266729 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq266729
  have eq266908 : y = (M.op x y) ∨ x = y := by grind
  clear eq266907
  have eq266926 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq265404
       have i₂ := eq266908
       grind)
    | exact superpose eq266908 eq265404
    | exact resolve eq265404 eq266908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq265404 eq266908
  have eq267056 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq266926
  have eq267057 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq267056
  have eq267138 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq267057
       grind)
    | exact superpose eq267057 eq10
    | exact resolve eq10 eq267057
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267057
  have eq267316 : x = y ∨ x = y := by
    first
    | (have i₁ := eq267138
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq267138
    | exact resolve eq267138 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267138
  have eq267317 : x = y := by grind
  clear eq267316
  have eq267331 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq267317
       grind)
    | exact superpose eq267317 eq16
    | exact resolve eq16 eq267317
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267317
  have eq267777 : False := by grind
  exact eq267777

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pxy_pyx_pxy_pyx_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
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
  have eq86 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
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
  have eq228 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq86 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq86 X0 X1
       grind)
    | exact superpose eq86 eq13
    | (have j0 := eq13 (σ X0) (σ X1)
       have j1 := eq86 X0 X1
       grind)
    | (have r₁ := eq13 (σ X1) (σ X0)
       have r₂ := eq86 X0 X1
       grind)
    | (have r₁ := eq13 (σ X0) (σ X1)
       have r₂ := eq86 X0 X1
       grind)
    | exact resolve eq13 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq229 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq86 X0 X1
       grind)
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq86 X0 X1
       grind)
    | exact superpose eq86 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       have j1 := eq86 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq86 X0 X1
       grind)
    | exact resolve eq12 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq232 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have j0 := eq228 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq228
  have eq237 : ∀ X0 X1 : G, (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq229 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq229 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq229 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq229
  have eq238 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq232 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq232 X0 X0
       have r₂ := eq12 (σ X0) (σ X0)
       grind)
    | (have r₁ := eq232 X0 X1
       have r₂ := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq232 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq232
  have eq247 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq237 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq237
    | (have j0 := eq237 X0 X1
       grind)
    | exact resolve eq237 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq237
  have eq248 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) ≠ (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq247 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq247
  have eq249 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq238 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq238
    | (have j0 := eq238 X0 X1
       grind)
    | exact resolve eq238 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq238
  have eq250 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq249 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249
  have eq255 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq250 X0 X1
       have j1 := eq248 X0 X1
       grind)
    | (have r₁ := eq250 X0 X1
       have r₂ := eq248 X0 X1
       grind)
    | exact resolve eq250 eq248
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq248 eq250
  have eq256 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq255 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq255
    | exact resolve eq255 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq267 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq255 x y
       grind)
    | exact superpose eq255 eq16
    | exact resolve eq16 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq354 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq256 X0 (τ X1)
       grind)
    | exact superpose eq256 eq18
    | exact resolve eq18 eq256
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq256
  have eq377 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq354 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq354
    | exact resolve eq354 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq354
  have eq388 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq377 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq377
    | exact resolve eq377 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq377
  have eq415 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq267
       have i₂ := eq388 x y
       grind)
    | exact superpose eq388 eq267
    | exact resolve eq267 eq388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq267 eq388
  have eq416 : False := by grind
  exact eq416

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(X,Y) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pxy_pyx_pxy_Equation630 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law630 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X1 X1) = X1 := by
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
  have eq52 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq52 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq52 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq52 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq52
  have eq55 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq53 (σ X0)
       grind)
    | exact superpose eq53 eq15
    | exact resolve eq15 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq64 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq55 X0
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq55
    | exact resolve eq55 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53 eq55
  have eq75 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op X1 (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq64 X0
       grind)
    | exact superpose eq64 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq84 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) := by
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
  have eq90 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq84 X0 X1
       have i₂ := eq64 X1
       grind)
    | exact superpose eq64 eq84
    | (have j0 := eq84 X0 X1
       grind)
    | exact resolve eq84 eq64
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq64 eq84
  have eq178 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X1) (σ X0)
       have i₂ := eq90 X0 X1
       grind)
    | (have i₁ := eq13 (σ X0) (σ X1)
       have i₂ := eq90 X0 X1
       grind)
    | exact superpose eq90 eq13
    | (have j0 := eq13 X0 (σ X1)
       have j1 := eq90 X0 X1
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
  have eq182 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq178 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq186 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq182 X0 X1
       have j1 := eq12 (σ X0) (σ X1)
       grind)
    | (have r₁ := eq182 X0 X1
       have r₂ := eq12 X0 (σ X1)
       grind)
    | exact resolve eq182 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq196 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq186 X0 X1
       have j1 := eq75 X1 (σ X0)
       grind)
    | (have r₁ := eq186 X0 X0
       have r₂ := eq75 X0 X1
       grind)
    | exact resolve eq186 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq186
  have eq203 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq196 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq196
    | (have j0 := eq196 X0 X1
       grind)
    | exact resolve eq196 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq196
  have eq204 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq203 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203
  have eq210 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq204 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq204
    | exact resolve eq204 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq221 : (σ (M.op x y)) ≠ (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq204 x y
       grind)
    | exact superpose eq204 eq16
    | exact resolve eq16 eq204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq204
  have eq297 : ∀ X0 X1 : G, (k (σ (τ X0)) X1) = (M.op X0 (σ (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq210 X0 (τ X1)
       grind)
    | exact superpose eq210 eq18
    | exact resolve eq18 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq210
  have eq316 : ∀ X0 X1 : G, (M.op X0 X1) = (k (σ (τ X0)) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq297 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq297
    | exact resolve eq297 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq297
  have eq325 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq316 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq316
    | exact resolve eq316 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq316
  have eq346 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq221
       have i₂ := eq325 x y
       grind)
    | exact superpose eq325 eq221
    | exact resolve eq221 eq325
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq221 eq325
  have eq347 : False := by grind
  exact eq347

/-- `Equation630`: `x = x ◇ (y ◇ ((x ◇ x) ◇ y))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyx_pxx_pxy_pyx_Equation630 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law630 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law630.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq28 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  clear eq18
  have eq37 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq45 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq28
    | exact resolve eq28 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq451 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3062 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq451 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq451
    | exact resolve eq451 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq451
  have eq3118 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq3062 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq3062
    | (have j0 := eq3062 X0 X1
       grind)
    | exact resolve eq3062 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3062
  have eq3131 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) = (σ (M.op (τ X1) (τ X0))) ∨ (M.op (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3118 (τ X1) (τ X0)
       have i₂ := eq45 X1 X0
       grind)
    | exact superpose eq45 eq3118
    | (have j0 := eq3118 (τ X1) (τ X0)
       grind)
    | exact resolve eq3118 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3118
  have eq3224 : ∀ X0 X1 : G, (M.op (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (k X0 X1) = (σ (M.op (τ X1) (τ X0))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq3131 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq3131
    | (have j0 := eq3131 X0 X1
       grind)
    | exact resolve eq3131 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3131
  have eq18858 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) ∨ (τ X0) = (τ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X1) (τ X0)
       have i₂ := eq3224 X0 X1
       grind)
    | (have i₁ := eq13 (τ X0) (τ X1)
       have i₂ := eq3224 X0 X1
       grind)
    | exact superpose eq3224 eq13
    | (have j0 := eq13 (τ X0) (τ X1)
       have j1 := eq3224 X1 X0
       grind)
    | (have r₁ := eq13 (τ X1) (τ X0)
       have r₂ := eq3224 X0 X1
       grind)
    | (have r₁ := eq13 (τ X0) (τ X1)
       have r₂ := eq3224 X0 X1
       grind)
    | exact resolve eq13 eq3224
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3224
  have eq18859 : ∀ X0 X1 : G, (M.op (τ X0) (τ X1)) ≠ (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq18858 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18858
  have eq18860 : ∀ X0 X1 : G, (τ X0) = (τ X1) ∨ (k (τ X1) (τ X0)) = (M.op (τ X0) (τ X1)) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have j0 := eq18859 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18859
  have eq18877 : ∀ X0 X1 : G, (τ (k X1 X0)) = (M.op (τ X0) (τ X1)) ∨ (τ X0) = (τ X1) ∨ (k X1 X0) = (σ (M.op (τ X0) (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18860 X0 X1
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq18860
    | (have j0 := eq18860 X0 X1
       grind)
    | exact resolve eq18860 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq18860
  have eq18915 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k (σ X0) X1) = (σ (M.op (τ X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18877 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18877
    | exact resolve eq18877 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18877
  have eq18985 : ∀ X0 X1 : G, (k (σ X0) X1) = (σ (M.op (τ X1) X0)) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq18915 X0 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq18915
    | (have j0 := eq18915 X0 X1
       grind)
    | exact resolve eq18915 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18915
  have eq19046 : ∀ X0 X1 : G, (τ (k (σ X0) X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op (τ X1) X0)
       have i₂ := eq18985 X0 X1
       grind)
    | exact superpose eq18985 eq10
    | (have j1 := eq18985 X0 X1
       grind)
    | exact resolve eq10 eq18985
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18985
  have eq19154 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 ∨ (k X0 (τ X1)) = (M.op (τ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq19046 X0 X1
       have i₂ := eq37 X0 X1
       grind)
    | exact superpose eq37 eq19046
    | (have j0 := eq19046 X0 X1
       grind)
    | exact resolve eq19046 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq19046
  have eq19155 : ∀ X0 X1 : G, (k X0 (τ X1)) = (M.op (τ X1) X0) ∨ (τ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq19154 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19154
  have eq19204 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19155 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19155
    | exact resolve eq19155 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq19243 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq19155 X1 X0
       grind)
    | exact superpose eq19155 eq19
    | (have j1 := eq19155 X1 X0
       grind)
    | exact resolve eq19 eq19155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq19155
  have eq19558 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq19204 (σ X0) (σ X1)
       grind)
    | exact superpose eq19204 eq15
    | (have j1 := eq19204 (σ (k X1 X0)) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq19204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19204
  have eq19689 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19243 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq19243
    | exact resolve eq19243 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19243
  have eq19863 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19689 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq19689
    | (have j0 := eq19689 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq19689 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19689
  have eq21292 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq19558 x y
       grind)
    | exact superpose eq19558 eq16
    | (have j1 := eq19558 x y
       grind)
    | exact resolve eq16 eq19558
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19558
  have eq21340 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq21292
       have i₂ := eq19863 x y
       grind)
    | exact superpose eq19863 eq21292
    | (have j1 := eq19863 (σ x) (σ y)
       grind)
    | (have r₁ := eq21292
       have r₂ := eq19863 x y
       grind)
    | (have r₁ := eq21292
       have r₂ := eq19863 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq21292
       have r₂ := eq19863 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq21292 eq19863
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19863 eq21292
  have eq21343 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq21340
  have eq21346 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21343
       grind)
    | exact superpose eq21343 eq16
    | exact resolve eq16 eq21343
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21343
  have eq21347 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq21346
       have r₂ := eq22 x
       grind)
    | exact resolve eq21346 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21346
  have eq21348 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21347
       grind)
    | exact superpose eq21347 eq16
    | exact resolve eq16 eq21347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21349 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq21347
       grind)
    | exact superpose eq21347 eq10
    | exact resolve eq10 eq21347
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21347
  have eq21518 : x = y := by
    first
    | (have i₁ := eq21349
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq21349
    | exact resolve eq21349 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21349
  have eq21519 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq21348
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq21348
    | exact resolve eq21348 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq21348
  have eq21520 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq21519
       have i₂ := eq21518
       grind)
    | exact superpose eq21518 eq21519
    | exact resolve eq21519 eq21518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21518 eq21519
  have eq21521 : False := by grind
  exact eq21521
