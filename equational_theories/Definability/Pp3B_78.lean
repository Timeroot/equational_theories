import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_x_y_pyx_pxx_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) = (M.op (M.op X1 X2) X0) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ X0 ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq19 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
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
  have eq26 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X0 X3) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 X0 X3
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq9 X2 X0 X2
       have i₂ := eq9 X0 X2 X2
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) (τ X0)) (τ X0))) := by
    intro X0
    grind
  clear eq19
  have eq53 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq20
  have eq54 : ∀ X0 : G, (τ X0) = (M.op (τ X0) (τ X0)) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq53 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq53
    | (have j0 := eq53 X0
       grind)
    | exact resolve eq53 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq72 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
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
  have eq96 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 X3) X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26 X2 X2 X0 X3
       have i₂ := eq9 X2 X0 X1
       grind)
    | (have i₁ := eq26 X1 X2 X0 X3
       have i₂ := eq9 X0 X1 X2
       grind)
    | exact superpose eq9 eq26
    | exact resolve eq26 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq503 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq72 y x
       grind)
    | exact superpose eq72 eq16
    | (have j1 := eq72 x y
       grind)
    | exact resolve eq16 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72
  have eq599 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq40 X0
       have i₂ := eq54 X0
       grind)
    | exact superpose eq54 eq40
    | (have j1 := eq54 X0
       grind)
    | exact resolve eq40 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq616 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) ∨ (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq599 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq599
    | (have j0 := eq599 X0
       grind)
    | exact resolve eq599 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq599
  have eq617 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq616 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq616
  have eq619 : ∀ X0 : G, (k (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq617 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq617
    | exact resolve eq617 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq639 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq619 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq619
    | exact resolve eq619 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq619
  have eq646 : ∀ X0 : G, (k X0 X0) = (τ (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq10 (k X0 X0)
       have i₂ := eq639 X0
       grind)
    | exact superpose eq639 eq10
    | exact resolve eq10 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq675 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq646 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq646
    | exact resolve eq646 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq646
  have eq716 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq675 (σ X0)
       grind)
    | exact superpose eq675 eq15
    | exact resolve eq15 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq731 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq716 X0
       have i₂ := eq639 X0
       grind)
    | exact superpose eq639 eq716
    | exact resolve eq716 eq639
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq639 eq716
  have eq790 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq503
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq503
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq503
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq503
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq503 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq503
  have eq791 : (σ x) = (σ y) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = y ∨ x = (M.op y y) := by grind
  clear eq790
  have eq923 : ∀ X0 X1 : G, (k X0 (σ (M.op (τ X0) (τ X0)))) = (σ (M.op (M.op (τ X0) X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq40 X0
       have i₂ := eq96 (τ X0) (τ X0) (τ X0) X1
       grind)
    | (have i₁ := eq40 X0
       have i₂ := eq96 (τ X0) X1 (τ X0) (τ X0)
       grind)
    | exact superpose eq96 eq40
    | exact resolve eq40 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq96
  have eq940 : ∀ X0 X1 : G, (k X0 (k X0 X0)) = (σ (M.op (M.op (τ X0) X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq923 X0 X1
       have i₂ := eq617 X0
       grind)
    | exact superpose eq617 eq923
    | exact resolve eq923 eq617
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617 eq923
  have eq945 : ∀ X0 X1 : G, (k X0 (M.op X0 X0)) = (σ (M.op (M.op (τ X0) X1) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq940 X0 X1
       have i₂ := eq675 X0
       grind)
    | exact superpose eq675 eq940
    | exact resolve eq940 eq675
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq675 eq940
  have eq997 : ∀ X0 X1 X2 : G, (M.op (M.op X1 X2) (σ X0)) = (M.op (σ (M.op X0 X0)) X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X1 X2
       have i₂ := eq731 X0
       grind)
    | exact superpose eq731 eq9
    | exact resolve eq9 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5081 : ∀ X0 X1 : G, (k (σ X0) (M.op (σ X0) (σ X0))) = (σ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq945 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq945
    | exact resolve eq945 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq945
  have eq5159 : ∀ X0 X1 : G, (M.op (M.op (σ X0) (σ X0)) (σ X0)) = (σ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    grind
  clear eq5081
  have eq5180 : ∀ X0 X1 : G, (M.op (σ (M.op X0 X0)) (σ X0)) = (σ (M.op (M.op X0 X1) X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5159 X0 X1
       have i₂ := eq997 X0 (σ X0) (σ X0)
       grind)
    | exact superpose eq997 eq5159
    | exact resolve eq5159 eq997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq997 eq5159
  have eq92857 : x = y ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq791
       have i₂ := eq731 y
       grind)
    | exact superpose eq731 eq791
    | exact resolve eq791 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq791
  have eq92858 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq92857
       grind)
    | exact superpose eq92857 eq16
    | exact resolve eq16 eq92857
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92857
  have eq92859 : (σ x) = (σ y) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq92858
       have r₂ := eq731 x
       grind)
    | exact resolve eq92858 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92858
  have eq673865 : y = (τ (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq92859
       grind)
    | exact superpose eq92859 eq10
    | exact resolve eq10 eq92859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92859
  have eq674143 : x = y ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq673865
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq673865
    | exact resolve eq673865 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq673865
  have eq674175 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq674143
       grind)
    | exact superpose eq674143 eq16
    | exact resolve eq16 eq674143
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674143
  have eq674186 : (σ x) = (σ (M.op y y)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq674175
       have r₂ := eq731 x
       grind)
    | exact resolve eq674175 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731 eq674175
  have eq674554 : (M.op y y) = (τ (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq674186
       grind)
    | exact superpose eq674186 eq10
    | exact resolve eq10 eq674186
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674186
  have eq674818 : x = (M.op y y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq674554
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq674554
    | exact resolve eq674554 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq674554
  have eq674819 : x = (M.op y y) := by grind
  clear eq674818
  have eq675496 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq5180 y y
       have i₂ := eq674819
       grind)
    | exact superpose eq674819 eq5180
    | exact resolve eq5180 eq674819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5180 eq674819
  have eq675668 : False := by grind
  exact eq675668

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = Y then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_y_pxy_pyy_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a ≠ b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  clear eq24 eq36
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
  have eq115 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
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
  have eq121 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
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
  have eq122 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq20 eq121
    | exact resolve eq121 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq121
  have eq123 : x = (M.op x y) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y x) := by
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
  have eq124 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
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
  have eq419 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op X2 X2) X4) X3) := by
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
  have eq423 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (M.op X0 X0) X2) X1) := by
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
  have eq425 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 X1) X2) = (M.op (M.op X2 X3) X0) := by
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
  have eq493 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) (M.op x y)) := by
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
  have eq495 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq493 X0
       have i₂ := eq245 x sF0
       grind)
    | exact superpose eq245 eq493
    | exact resolve eq493 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493
  have eq544 : ∀ X0 X1 X2 X3 X4 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op (M.op X3 X4) X2) X0) := by
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
  clear eq51 eq55
  have eq809 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (M.op x y) X0) (σ x)) := by
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
  clear eq429
  have eq856 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq430 eq809
    | exact resolve eq809 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809
  have eq1749 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (σ y) (σ y)) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq78 (M.op y y)
       have i₂ := eq113
       grind)
    | exact superpose eq113 eq78
    | exact resolve eq78 eq113
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113
  have eq1755 : (σ (M.op (k x x) (k x x))) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) := by
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
  have eq1807 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op (k x x) (k x x))) := by
    first
    | (have i₁ := eq1755
       have i₂ := eq71 sF2
       grind)
    | exact superpose eq71 eq1755
    | exact resolve eq1755 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1755
  have eq1810 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq1807
       have i₂ := eq71 x
       grind)
    | exact superpose eq71 eq1807
    | exact resolve eq1807 eq71
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71 eq1807
  have eq1812 : (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) = (σ (M.op (M.op x y) (M.op x x))) := by
    first
    | (have i₁ := eq1810
       have i₂ := eq245 x (M.op x x)
       grind)
    | exact superpose eq245 eq1810
    | exact resolve eq1810 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1810
  have eq1814 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq495 eq1812
    | exact resolve eq1812 eq495
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq495 eq1812
  have eq1816 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq255 eq1814
    | exact resolve eq1814 eq255
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1814
  have eq1818 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq856 eq1816
    | exact resolve eq1816 eq856
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq856 eq1816
  have eq1819 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq145 eq1818
    | exact resolve eq1818 eq145
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq145 eq1818
  have eq2147 : ∀ X0 X1 : G, (M.op (M.op X0 X1) (M.op (σ x) (σ y))) = (M.op (M.op (σ (M.op x y)) (σ (M.op x y))) X0) := by
    intro X0 X1
    first
    | exact superpose eq1819 eq425
    | exact resolve eq425 eq1819
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1819
  have eq2885 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (M.op (σ x) (σ y)) X0) X1) := by
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
  have eq2895 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2885 X1 X2
       have i₂ := eq425 sF4 X1 X2 x
       grind)
    | (have i₁ := eq2885 x X0
       have i₂ := eq425 X0 X1 sF4 x
       grind)
    | exact superpose eq425 eq2885
    | exact resolve eq2885 eq425
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425 eq2885
  have eq3659 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op x y)) = (M.op (M.op X0 X2) (M.op (σ x) (σ y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2895 X1 X1 sF0
       have i₂ := eq14 sF0 X1 X2
       grind)
    | (have i₁ := eq2895 X0 X1 X2
       have i₂ := eq14 X0 sF0 X2
       grind)
    | exact superpose eq14 eq2895
    | exact resolve eq2895 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4849 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (M.op (σ x) (σ y))) = (M.op (M.op X0 X1) (σ (M.op x y))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq2147 X1 X1
       have i₂ := eq14 sF1 X1 X2
       grind)
    | (have i₁ := eq2147 X0 X1
       have i₂ := eq14 X0 sF1 sF1
       grind)
    | exact superpose eq14 eq2147
    | exact resolve eq2147 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2147
  have eq10152 : ∀ X0 X1 X2 X3 : G, (M.op (M.op (M.op X0 X1) X2) X3) = (M.op (M.op (M.op x y) X2) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq419 X0 X1 X2 X3 x
       have i₂ := eq423 X2 X3 x
       grind)
    | exact superpose eq423 eq419
    | exact resolve eq419 eq423
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419 eq423
  have eq13346 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (M.op X2 X2)) = (M.op (M.op (M.op x y) X2) X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq544 X0 X1 X2 x x
       have i₂ := eq10152 x x X2 X0
       grind)
    | (have i₁ := eq544 x X1 X2 x y
       have i₂ := eq10152 X0 X1 X2 x
       grind)
    | exact superpose eq10152 eq544
    | (have j0 := eq544 X0 X1 X2 x y
       grind)
    | exact resolve eq544 eq10152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq544 eq10152
  have eq43864 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq124 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq43865 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq43864
    | exact resolve eq43864 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43864
  have eq43876 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq43865
       have r₂ := eq27
       grind)
    | exact resolve eq43865 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43865
  have eq43880 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq43876
    | exact resolve eq43876 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43876
  have eq43882 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq26 eq43880
    | exact resolve eq43880 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43880
  have eq44258 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq43882 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq43882
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq43882
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq43882
       grind)
    | exact resolve eq13 eq43882
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43882
  have eq44360 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | (have r₁ := eq44258
       have r₂ := eq26
       grind)
    | exact resolve eq44258 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44258
  have eq44398 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) := by
    first
    | exact superpose eq44360 eq124
    | exact resolve eq124 eq44360
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq44360
  have eq44406 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (M.op x y) = (M.op y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq44398
  have eq44408 : (M.op x y) = (M.op y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq44406
       have r₂ := eq27
       grind)
    | exact resolve eq44406 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44406
  have eq44413 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq44408
       grind)
    | exact superpose eq44408 eq13
    | (have r₁ := eq13 x y
       have r₂ := eq44408
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq44408
       grind)
    | exact resolve eq13 eq44408
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44408
  have eq44490 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq44413
       have r₂ := eq18
       grind)
    | exact resolve eq44413 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44413
  have eq44509 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq106
       have i₂ := eq44490
       grind)
    | exact superpose eq44490 eq106
    | exact resolve eq106 eq44490
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq44490
  have eq44523 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq44509
    | exact resolve eq44509 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44509
  have eq44557 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq44523 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq44523
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44560 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq44557
    | exact resolve eq44557 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44557
  have eq44571 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq44560
       have r₂ := eq27
       grind)
    | exact resolve eq44560 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44560
  have eq44575 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq44571
    | exact resolve eq44571 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44571
  have eq44576 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq44575
  have eq44579 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq44576
    | exact resolve eq44576 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44576
  have eq44609 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44579 eq13
    | (have r₁ := eq13 (σ x) (σ y)
       have r₂ := eq44579
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq44579
       grind)
    | exact resolve eq13 eq44579
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44579
  have eq44711 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq44609
       have r₂ := eq26
       grind)
    | exact resolve eq44609 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44609
  have eq44757 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44711 eq44523
    | exact resolve eq44523 eq44711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44523 eq44711
  have eq44759 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq44757
  have eq44763 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq44759
       have r₂ := eq27
       grind)
    | exact resolve eq44759 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44759
  have eq44787 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ x)) = (M.op (M.op (M.op x y) X2) X0) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq44763 eq2895
    | exact resolve eq2895 eq44763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2895
  have eq44792 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X2) (σ x)) = (M.op (M.op X0 X1) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq44763 eq3659
    | exact resolve eq3659 eq44763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3659
  have eq44795 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) (σ x)) = (M.op (M.op X0 X2) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0 X1 X2
    first
    | exact superpose eq44763 eq4849
    | exact resolve eq4849 eq44763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44843 : ∀ X0 X2 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X0 X2) (σ (M.op x y))) ∨ x = (M.op x y) := by
    intro X0 X2
    first
    | exact superpose eq430 eq44795
    | exact resolve eq44795 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44795
  have eq44846 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X0 X1) (M.op x y)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq430 eq44792
    | exact resolve eq44792 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44792
  have eq44848 : ∀ X0 X2 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op (M.op x y) X2) X0) ∨ x = (M.op x y) := by
    intro X0 X2
    first
    | exact superpose eq430 eq44787
    | exact resolve eq44787 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44787
  have eq59971 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X0 X1) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq4849 eq44843
    | exact resolve eq44843 eq4849
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4849 eq44843
  have eq67954 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op X0 X1) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | exact superpose eq44763 eq59971
    | exact resolve eq59971 eq44763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59971
  have eq68169 : ∀ X0 X1 : G, (M.op (σ x) X0) = (M.op (M.op X0 X1) (σ x)) ∨ x = (M.op x y) := by
    intro X0 X1
    first
    | (have j0 := eq67954 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67954
  have eq68371 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (σ x) X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq430 eq68169
    | exact resolve eq68169 eq430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq430 eq68169
  have eq178899 : (σ (M.op (M.op y y) (M.op y y))) = (M.op (M.op (M.op x y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq1749
       have i₂ := eq13346 sF3 sF3 sF3
       grind)
    | exact superpose eq13346 eq1749
    | exact resolve eq1749 eq13346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1749
  have eq178900 : (M.op (M.op (M.op x y) (σ y)) (σ y)) = (σ (M.op (M.op (M.op x y) y) y)) := by
    first
    | (have i₁ := eq178899
       have i₂ := eq13346 y y y
       grind)
    | exact superpose eq13346 eq178899
    | exact resolve eq178899 eq13346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13346 eq178899
  have eq178901 : (σ (M.op (M.op y y) (M.op x y))) = (M.op (M.op (M.op x y) (σ y)) (σ y)) := by
    first
    | (have i₁ := eq178900
       have i₂ := eq14 y sF0 y
       grind)
    | exact superpose eq14 eq178900
    | exact resolve eq178900 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178900
  have eq178903 : (M.op (M.op (M.op x y) (σ y)) (σ y)) = (σ (M.op (M.op (σ x) (σ y)) y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44846 eq178901
    | exact resolve eq178901 eq44846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44846
  have eq179097 : (M.op (M.op (σ x) (σ y)) (σ y)) = (σ (M.op (M.op (σ x) (σ y)) y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq178903 eq44848
    | exact resolve eq44848 eq178903
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44848 eq178903
  have eq179243 : (M.op (M.op (σ x) (σ y)) (σ y)) = (σ (M.op (M.op (σ x) (σ y)) y)) ∨ x = (M.op x y) := by grind
  clear eq179097
  have eq179387 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44763 eq179243
    | exact resolve eq179243 eq44763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179397 : (M.op (M.op (σ x) (σ y)) y) = (τ (M.op (M.op (σ x) (σ y)) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq179243 eq16
    | exact resolve eq16 eq179243
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179243
  have eq179479 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) y)) ∨ x = (M.op x y) := by grind
  clear eq179387
  have eq179503 : (M.op (σ x) (σ y)) = (σ (M.op (σ x) y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq179479
    | exact resolve eq179479 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179479
  have eq179577 : (τ (M.op (σ x) (σ y))) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq179503 eq16
    | exact resolve eq16 eq179503
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179503
  have eq180858 : (τ (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq68371 eq179397
    | exact resolve eq179397 eq68371
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68371 eq179397
  have eq180927 : (τ (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) y) ∨ x = (M.op x y) := by grind
  clear eq180858
  have eq180937 : (τ (M.op (σ x) (σ y))) = (M.op (M.op (σ x) (σ y)) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq180927
    | exact resolve eq180927 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180927
  have eq180950 : (τ (σ x)) = (M.op (σ x) y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq44763 eq180937
    | exact resolve eq180937 eq44763
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44763
  have eq181094 : (τ (σ x)) = (M.op (σ x) y) ∨ x = (M.op x y) := by grind
  clear eq180950
  have eq181153 : x = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq28 eq181094
    | exact resolve eq181094 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq181094
  have eq181599 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq181153 eq179577
    | exact resolve eq179577 eq181153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179577
  have eq181601 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op x X0) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq181153 eq255
    | exact resolve eq255 eq181153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255 eq181153
  have eq181741 : x = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq181599
  have eq182610 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq181601 eq180937
    | exact resolve eq180937 eq181601
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180937 eq181601
  have eq182874 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by grind
  clear eq182610
  have eq183037 : (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq182874
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq182874
    | exact resolve eq182874 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182874
  have eq183294 : x = (M.op x y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq183037 eq181741
    | exact resolve eq181741 eq183037
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181741 eq183037
  have eq183351 : x = (M.op x y) := by grind
  clear eq183294
  have eq183379 : (σ x) = (σ (M.op x y)) := by
    first
    | exact superpose eq183351 eq20
    | exact resolve eq20 eq183351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq183560 : (σ (M.op (M.op y y) x)) = (M.op (M.op x (σ y)) (σ y)) := by
    first
    | exact superpose eq183351 eq178901
    | exact resolve eq178901 eq183351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178901
  have eq183564 : (M.op (M.op x y) (σ y)) = (σ (M.op (M.op y y) x)) := by
    first
    | (have i₁ := eq183560
       have i₂ := eq245 sF3 sF3
       grind)
    | exact superpose eq245 eq183560
    | exact resolve eq183560 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183560
  have eq183711 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq183379
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq183379
    | exact resolve eq183379 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq183379
  have eq183713 : (M.op (M.op x y) (σ y)) = (σ (M.op (M.op x x) y)) := by
    first
    | (have i₁ := eq183564
       have i₂ := eq14 x y y
       grind)
    | (have i₁ := eq183564
       have i₂ := eq14 y x x
       grind)
    | exact superpose eq14 eq183564
    | exact resolve eq183564 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183564
  have eq183813 : (σ (M.op (M.op x y) y)) = (M.op (M.op x y) (σ y)) := by
    first
    | (have i₁ := eq183713
       have i₂ := eq245 x y
       grind)
    | exact superpose eq245 eq183713
    | exact resolve eq183713 eq245
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183713
  have eq183854 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq183351 eq183813
    | exact resolve eq183813 eq183351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183813
  have eq183894 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq183854
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq183854
    | exact resolve eq183854 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq183854
  have eq183932 : (σ (M.op x y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq20 eq183894
    | exact resolve eq183894 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq183894
  have eq184853 : (M.op (σ x) (σ y)) = (M.op (σ (M.op x y)) (σ y)) := by
    first
    | exact superpose eq183711 eq26
    | exact resolve eq26 eq183711
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq183711
  have eq185477 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq183932 eq245
    | exact resolve eq245 eq183932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq245
  have eq185657 : ∀ X0 : G, (M.op x X0) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq183351 eq185477
    | exact resolve eq185477 eq183351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183351 eq185477
  have eq191181 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq185657 eq184853
    | exact resolve eq184853 eq185657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184853 eq185657
  have eq191494 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq183932 eq191181
    | exact resolve eq191181 eq183932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183932 eq191181
  have eq191630 : False := by grind
  exact eq191630

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyy_x_y_pyx_x_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = M.op b b ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) ≠ (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq38 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X1) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq12
    | (have j0 := eq12 (σ X0) (σ X1)
       grind)
    | exact resolve eq12 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op (τ X1) X0) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 X0
       have i₂ := eq12 (τ X1) X0
       grind)
    | exact superpose eq12 eq18
    | (have j1 := eq12 (τ X1) X0
       grind)
    | exact resolve eq18 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq51 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ X0 = X1 := by
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
    | (have r₁ := eq14 (M.op X0 X1) (M.op X1 X1)
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq65 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq51 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq51
    | (have j0 := eq51 (σ (k X0 X1)) (M.op (σ X1) (σ X0))
       grind)
    | exact resolve eq51 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq297 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq65 y x
       grind)
    | exact superpose eq65 eq16
    | (have j1 := eq65 x y
       grind)
    | exact resolve eq16 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65
  have eq327 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq297
       have i₂ := eq51 y x
       grind)
    | exact superpose eq51 eq297
    | (have j1 := eq51 (σ x) (σ y)
       grind)
    | (have r₁ := eq297
       have r₂ := eq51 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq297
       have r₂ := eq51 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq297 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq297
  have eq332 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq327
  have eq419 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq332
       grind)
    | exact superpose eq332 eq16
    | exact resolve eq16 eq332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq332
  have eq433 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have j0 := eq38 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq612 : ∀ X0 : G, (k X0 (σ (τ X0))) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have j0 := eq40 (τ X0) X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq613 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq612 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq612
    | exact resolve eq612 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq612
  have eq617 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq613 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq613
    | exact resolve eq613 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq643 : ∀ X0 : G, (σ (k X0 X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq617 X0
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq617
    | exact resolve eq617 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq617
  have eq706 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq433 X0
       have i₂ := eq643 X0
       grind)
    | exact superpose eq643 eq433
    | exact resolve eq433 eq643
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq433 eq643
  have eq6016 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq419
       have r₂ := eq706 x
       grind)
    | exact resolve eq419 eq706
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq419
  have eq6018 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6016
       grind)
    | exact superpose eq6016 eq10
    | exact resolve eq10 eq6016
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6016
  have eq6055 : x = y := by
    first
    | (have i₁ := eq6018
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6018
    | exact resolve eq6018 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6018
  have eq6057 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6055
       grind)
    | exact superpose eq6055 eq16
    | exact resolve eq16 eq6055
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6055
  have eq6058 : False := by grind
  exact eq6058

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(X,X) = m(Y,X) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pxx_pyx_pyx_pxx_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq30 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq30 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq30 x
       have r₂ := eq12 x x
       grind)
    | exact resolve eq30 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30
  have eq39 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
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
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq40 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X0
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq12 X1 X0
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq14 X1 X0
       grind)
    | (have r₁ := eq12 (M.op X0 X0) X0
       have r₂ := eq14 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq14 X0 X1
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq44 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = X0 := by
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
    | (have r₁ := eq13 X1 (M.op X1 X1)
       have r₂ := eq14 (M.op X1 X1) X1
       grind)
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq49 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq44 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq50 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq49 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq51 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq56 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq50 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq50 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq50 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq60 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 (k X1 X1) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq40 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq61 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq51 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq51 X0 X0
       have r₂ := eq12 X0 X0
       grind)
    | (have r₁ := eq51 (k X1 X1) X1
       have r₂ := eq12 (k X1 X1) X1
       grind)
    | (have r₁ := eq51 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq51 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51
  have eq67 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) ≠ X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq60 X0 X1
       have i₂ := eq31 X1
       grind)
    | exact superpose eq31 eq60
    | (have j0 := eq60 X0 X1
       grind)
    | exact resolve eq60 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq60
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq61 X0 X1
       have i₂ := eq31 X1
       grind)
    | exact superpose eq31 eq61
    | (have j0 := eq61 X0 X1
       grind)
    | exact resolve eq61 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq61
  have eq70 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq68 X0 X1
       have j1 := eq67 X0 X1
       grind)
    | (have r₁ := eq68 X0 X1
       have r₂ := eq67 X0 X1
       grind)
    | exact resolve eq68 eq67
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq67 eq68
  have eq168 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq56 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq172 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq168 X0 X1
       have j1 := eq70 X1 X0
       grind)
    | (have r₁ := eq168 X1 X1
       have r₂ := eq70 X1 X1
       grind)
    | (have r₁ := eq168 X1 X0
       have r₂ := eq70 X0 X1
       grind)
    | exact resolve eq168 eq70
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70 eq168
  have eq406 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
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
  have eq412 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq406 X0 X1
       have i₂ := eq172 X1 X0
       grind)
    | exact superpose eq172 eq406
    | exact resolve eq406 eq172
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq172 eq406
  have eq414 : False := by grind
  exact eq414

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = X then m(Y,X) else if m(Y,X) = Y then Y else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_x_pyx_y_pyx_y_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = a ∨ M.op b a ≠ b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = a ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X1) = X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq335 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq14 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq14 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq14 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq336 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq335 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq335
    | (have j0 := eq335 (σ X0) (σ X1)
       grind)
    | exact resolve eq335 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq337 : ∀ X0 X1 : G, (τ (k X0 X1)) = (M.op (τ X1) (τ X0)) ∨ (τ X1) = (M.op (τ X1) (τ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq335 (τ X0) (τ X1)
       have i₂ := eq31 X1 X0
       grind)
    | exact superpose eq31 eq335
    | (have j0 := eq335 (τ X0) (τ X1)
       grind)
    | exact resolve eq335 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq3517 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (M.op (σ X0) (σ X1)) ∨ (M.op X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq336 X1 X0
       have i₂ := eq335 X1 X0
       grind)
    | exact superpose eq335 eq336
    | (have j0 := eq336 X1 X0
       have j1 := eq335 (σ X1) (σ X0)
       grind)
    | exact resolve eq336 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq336
  have eq7671 : ∀ X0 X1 : G, (τ X0) ≠ (τ (k X1 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq337 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq7681 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ (τ (σ X1)) ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7671 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7671
    | (have j0 := eq7671 (σ X1) (σ X0)
       grind)
    | exact resolve eq7671 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7671
  have eq7691 : ∀ X0 X1 : G, (τ (σ (k X0 X1))) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7681 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq7681
    | (have j0 := eq7681 X0 X1
       grind)
    | exact resolve eq7681 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7681
  have eq7693 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (τ (σ X1)) = (M.op (τ (σ X1)) (τ (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq7691 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq7691
    | (have j0 := eq7691 X0 X1
       grind)
    | exact resolve eq7691 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7691
  have eq7694 : ∀ X0 X1 : G, (τ (σ X1)) = (M.op (τ (σ X1)) X0) ∨ (k X0 X1) ≠ X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7693 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7693
    | (have j0 := eq7693 X0 X1
       grind)
    | exact resolve eq7693 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7693
  have eq7695 : ∀ X0 X1 : G, (k X0 X1) ≠ X1 ∨ (M.op X1 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq7694 X0 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq7694
    | (have j0 := eq7694 X0 X1
       grind)
    | exact resolve eq7694 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7694
  have eq7697 : ∀ X0 X1 : G, (σ (k X0 X1)) ≠ (σ X1) ∨ (σ X1) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq7695 (σ X0) (σ X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq7695
    | (have j0 := eq7695 (σ X0) (σ X1)
       grind)
    | exact resolve eq7695 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7695
  have eq21765 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq3517 x y
       grind)
    | exact superpose eq3517 eq16
    | (have j1 := eq3517 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq3517 x y
       grind)
    | exact resolve eq16 eq3517
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3517
  have eq21796 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq21765
  have eq21807 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21796
       grind)
    | exact superpose eq21796 eq16
    | exact resolve eq16 eq21796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21809 : (σ x) ≠ (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq21796
       grind)
    | exact superpose eq21796 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq21796
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq21796
       grind)
    | exact resolve eq13 eq21796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21834 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq21809
  have eq21837 : (σ x) = (σ (k y x)) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21834
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq21834
    | exact resolve eq21834 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21834
  have eq21839 : (σ (M.op x y)) = (σ x) ∨ (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq335 eq21837
    | (have j1 := eq335 (σ x) (σ y)
       grind)
    | exact resolve eq21837 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21837
  have eq21840 : (σ y) = (M.op (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq21839
       have r₂ := eq21807
       grind)
    | exact resolve eq21839 eq21807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21839
  have eq21842 : (σ y) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq21840
       grind)
    | exact superpose eq21840 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq21840
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq21840
       grind)
    | exact resolve eq12 eq21840
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21840
  have eq21869 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by grind
  clear eq21842
  have eq21870 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq21869
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq21869
    | exact resolve eq21869 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21869
  have eq21871 : (σ x) = (σ (k y x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq21796 eq21870
    | exact resolve eq21870 eq21796
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21796 eq21870
  have eq21872 : (σ (M.op x y)) = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq335 eq21871
    | (have j1 := eq335 y x
       grind)
    | exact resolve eq21871 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335 eq21871
  have eq21873 : x = (M.op x y) := by
    first
    | (have r₁ := eq21872
       have r₂ := eq21807
       grind)
    | exact resolve eq21872 eq21807
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21807 eq21872
  have eq21874 : (σ x) ≠ (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21873
       grind)
    | exact superpose eq21873 eq16
    | exact resolve eq16 eq21873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21876 : x ≠ x ∨ y = (M.op y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq21873
       grind)
    | exact superpose eq21873 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq21873
       grind)
    | exact resolve eq13 eq21873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21901 : y = (M.op y x) ∨ x = (k y x) := by grind
  clear eq21876
  have eq22195 : y ≠ y ∨ (M.op x y) = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq21901
       grind)
    | exact superpose eq21901 eq12
    | (have j0 := eq12 y x
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq21901
       grind)
    | exact resolve eq12 eq21901
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21901
  have eq22224 : (M.op x y) = (k y x) ∨ x = (k y x) := by grind
  clear eq22195
  have eq22227 : x = (k y x) ∨ x = (k y x) := by
    first
    | (have i₁ := eq22224
       have i₂ := eq21873
       grind)
    | exact superpose eq21873 eq22224
    | exact resolve eq22224 eq21873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21873 eq22224
  have eq22228 : x = (k y x) := by grind
  clear eq22227
  have eq22235 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq7697 y x
       have i₂ := eq22228
       grind)
    | exact superpose eq22228 eq7697
    | (have j0 := eq7697 y x
       grind)
    | exact resolve eq7697 eq22228
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7697 eq22228
  have eq22240 : (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq22235
  have eq22248 : False := by grind
  exact eq22248

/-- `Equation4610`: `(x ◇ x) ◇ y = (y ◇ z) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_pyy_y_pyx_x_pyx_Equation4610 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law4610 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4610.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq69 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X2) ≠ (M.op (M.op X2 X2) (M.op X2 X2)) ∨ (M.op (M.op X0 X1) X2) = (k X0 (M.op X2 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | (have i₁ := eq13 X0 (M.op X1 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X0) X1) ≠ (M.op (M.op X1 X2) (M.op X1 X2)) ∨ (M.op (M.op X0 X0) X1) = (k X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X1 (M.op X0 X0)
       have i₂ := eq14 X0 X1 X2
       grind)
    | (have i₁ := eq13 X0 (M.op X1 X2)
       have i₂ := eq14 X0 X1 X2
       grind)
    | exact superpose eq14 eq13
    | exact resolve eq13 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq74 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq72 (σ X0)
       grind)
    | exact superpose eq72 eq10
    | exact resolve eq10 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq72 x
       grind)
    | exact superpose eq72 eq43
    | exact resolve eq43 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq76 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq72 sF2
       grind)
    | exact superpose eq72 eq49
    | exact resolve eq49 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq77 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq76
       have i₂ := eq72 x
       grind)
    | exact superpose eq72 eq76
    | exact resolve eq76 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76
  have eq78 : (M.op (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq75
       have i₂ := eq72 sF2
       grind)
    | exact superpose eq72 eq75
    | exact resolve eq75 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq79 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq72 X0
       grind)
    | exact superpose eq72 eq74
    | exact resolve eq74 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq89 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X1
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
  have eq95 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq96 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  clear eq24 eq36
  have eq98 : (σ (k y y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq96
       have i₂ := eq72 sF3
       grind)
    | exact superpose eq72 eq96
    | exact resolve eq96 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq100 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq98
       have i₂ := eq72 y
       grind)
    | exact superpose eq72 eq98
    | exact resolve eq98 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq119 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq95
       have i₂ := eq89 y x
       grind)
    | exact superpose eq89 eq95
    | (have j1 := eq89 x x
       grind)
    | exact resolve eq95 eq89
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq127 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq119
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq119
    | exact resolve eq119 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq129 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq20 eq127
    | exact resolve eq127 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq150 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq37
    | (have j0 := eq37 (M.op x y)
       grind)
    | exact resolve eq37 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq153 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq150
       have i₂ := eq72 sF1
       grind)
    | exact superpose eq72 eq150
    | exact resolve eq150 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq150
  have eq155 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by
    first
    | (have i₁ := eq153
       have i₂ := eq72 sF0
       grind)
    | exact superpose eq72 eq153
    | exact resolve eq153 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153
  have eq242 : ∀ X0 X1 : G, (M.op (M.op x X0) X1) = (M.op (M.op x y) X1) := by
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
  have eq393 : ∀ X0 X1 X2 : G, (σ (k (k X0 (τ X1)) X2)) = (k (k (σ X0) X1) (σ X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (k X0 (τ X1)) X2
       have i₂ := eq38 X1 X0
       grind)
    | exact superpose eq38 eq10
    | exact resolve eq10 eq38
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq395 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
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
  have eq410 : (M.op (M.op (σ x) (σ y)) x) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq54 eq242
    | exact resolve eq242 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq415 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op (M.op x y) (M.op x X0)) x) := by
    intro X0
    first
    | (have i₁ := eq53 (M.op x X0)
       have i₂ := eq242 X0 (M.op x X0)
       grind)
    | (have i₁ := eq53 (M.op x y)
       have i₂ := eq242 X0 (M.op x y)
       grind)
    | exact superpose eq242 eq53
    | exact resolve eq53 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq424 : ∀ X0 : G, (M.op (M.op x y) (M.op x X0)) = (M.op (M.op x x) (M.op x y)) := by
    intro X0
    first
    | (have i₁ := eq415 X0
       have i₂ := eq14 x sF0 (M.op x X0)
       grind)
    | exact superpose eq14 eq415
    | exact resolve eq415 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq415
  have eq427 : ∀ X0 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq424 X0
       have i₂ := eq242 x sF0
       grind)
    | exact superpose eq242 eq424
    | exact resolve eq424 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq424
  have eq456 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op (M.op X0 X0) X2) X1) := by
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
  have eq467 : ∀ X0 X1 : G, (M.op (M.op x y) X0) = (M.op (M.op X0 X1) x) := by
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
  have eq468 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op (M.op X0 X1) (σ x)) := by
    intro X0 X1
    first
    | exact superpose eq54 eq51
    | exact resolve eq51 eq54
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq54
  have eq533 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op (M.op x y) X0) x) := by
    intro X0 X1
    first
    | (have i₁ := eq467 (M.op X0 X1) x
       have i₂ := eq467 X0 X1
       grind)
    | (have i₁ := eq467 (M.op x y) X0
       have i₂ := eq467 X0 X1
       grind)
    | exact superpose eq467 eq467
    | exact resolve eq467 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq556 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op X0 X1)) = (M.op (M.op x x) (M.op x y)) := by
    intro X0 X1
    first
    | (have i₁ := eq533 sF0 X1
       have i₂ := eq14 sF0 x x
       grind)
    | (have i₁ := eq533 x X1
       have i₂ := eq14 x sF0 x
       grind)
    | exact superpose eq14 eq533
    | exact resolve eq533 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq533
  have eq566 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq556 X0 X1
       have i₂ := eq242 x sF0
       grind)
    | exact superpose eq242 eq556
    | exact resolve eq556 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq556
  have eq585 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (M.op x y) X0) (σ x)) := by
    intro X0 X1
    first
    | (have i₁ := eq468 (M.op X0 X1) x
       have i₂ := eq467 X0 X1
       grind)
    | (have i₁ := eq468 (M.op x y) X0
       have i₂ := eq467 X0 X1
       grind)
    | exact superpose eq467 eq468
    | exact resolve eq468 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq592 : (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) = (M.op (M.op (M.op x y) (σ x)) (σ x)) := by
    first
    | exact superpose eq410 eq468
    | exact resolve eq468 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq608 : (M.op (M.op (σ x) (σ y)) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq468 eq592
    | exact resolve eq592 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq592
  have eq613 : ∀ X0 X1 : G, (M.op (M.op (σ x) (σ y)) (M.op X0 X1)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0 X1
    first
    | exact superpose eq468 eq585
    | exact resolve eq585 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq585
  have eq804 : ∀ X0 X1 X2 : G, (M.op (M.op (M.op x y) X0) X1) = (M.op (M.op X1 X1) (M.op x X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X0 x X1 X2
       have i₂ := eq53 X0
       grind)
    | exact superpose eq53 eq56
    | exact resolve eq56 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1372 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) ≠ (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ y))) ∨ (M.op (M.op X0 X0) (σ x)) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq26 eq70
    | (have j0 := eq70 X0 (σ x) (σ y)
       grind)
    | exact resolve eq70 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq1386 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) ≠ (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ (M.op (M.op X0 X0) (σ x)) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq608 eq1372
    | (have j0 := eq1372 X0
       grind)
    | exact resolve eq1372 eq608
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608 eq1372
  have eq1396 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op (M.op (σ x) (σ y)) (M.op x y)) ∨ (M.op (M.op X0 X0) (σ x)) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq468 eq1386
    | (have j0 := eq1386 X0
       grind)
    | (have r₁ := eq1386 (M.op x y)
       have r₂ := eq468 (M.op x y) (M.op x y)
       grind)
    | exact resolve eq1386 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1386
  have eq1403 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (k X0 (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq468 eq1396
    | (have j0 := eq1396 X0
       grind)
    | exact resolve eq1396 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1396
  have eq1613 : (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) = (σ (M.op (k x x) (k x x))) := by
    first
    | (have i₁ := eq79 (k x x)
       have i₂ := eq43
       grind)
    | exact superpose eq43 eq79
    | exact resolve eq79 eq43
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq1660 : (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) = (σ (M.op (M.op x x) (M.op x x))) := by
    first
    | (have i₁ := eq1613
       have i₂ := eq72 x
       grind)
    | exact superpose eq72 eq1613
    | exact resolve eq1613 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1613
  have eq1663 : (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) = (σ (M.op (M.op x y) (M.op x x))) := by
    first
    | (have i₁ := eq1660
       have i₂ := eq242 x (M.op x x)
       grind)
    | exact superpose eq242 eq1660
    | exact resolve eq1660 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1660
  have eq1665 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (k (σ x) (σ x)) (k (σ x) (σ x))) := by
    first
    | exact superpose eq427 eq1663
    | exact resolve eq1663 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1663
  have eq1667 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ x)) (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq1665
       have i₂ := eq72 sF2
       grind)
    | exact superpose eq72 eq1665
    | exact resolve eq1665 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq1665
  have eq1669 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op (σ x) (σ x))) := by
    first
    | exact superpose eq249 eq1667
    | exact resolve eq1667 eq249
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq249 eq1667
  have eq1671 : (σ (M.op (M.op x y) (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq613 eq1669
    | exact resolve eq1669 eq613
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1669
  have eq1672 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq155 eq1671
    | exact resolve eq1671 eq155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1671
  have eq2259 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq129 eq89
    | (have j0 := eq89 x (σ x)
       grind)
    | exact resolve eq89 eq129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89 eq129
  have eq2260 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq26 eq2259
    | exact resolve eq2259 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2259
  have eq2263 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have r₁ := eq2260
       have r₂ := eq27
       grind)
    | exact resolve eq2260 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2260
  have eq2266 : (τ (σ x)) = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq2263 eq77
    | exact resolve eq77 eq2263
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77 eq2263
  have eq2317 : x = (M.op x x) ∨ x = (M.op x x) := by
    first
    | exact superpose eq28 eq2266
    | exact resolve eq2266 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2266
  have eq2318 : x = (M.op x x) := by grind
  clear eq2317
  have eq2332 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq78
       have i₂ := eq2318
       grind)
    | exact superpose eq2318 eq78
    | exact resolve eq78 eq2318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78
  have eq2337 : ∀ X0 : G, (M.op (M.op x y) X0) = (M.op x X0) := by
    intro X0
    first
    | (have i₁ := eq242 x X0
       have i₂ := eq2318
       grind)
    | exact superpose eq2318 eq242
    | exact resolve eq242 eq2318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2360 : (M.op x x) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq467 x x
       have i₂ := eq2318
       grind)
    | exact superpose eq2318 eq467
    | exact resolve eq467 eq2318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2370 : x = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq2360
       have i₂ := eq2318
       grind)
    | exact superpose eq2318 eq2360
    | exact resolve eq2360 eq2318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2360
  have eq2392 : (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq2332
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2332
    | exact resolve eq2332 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2332
  have eq2417 : (M.op (M.op x y) x) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2370 eq566
    | exact resolve eq566 eq2370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2422 : x = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq2370 eq2417
    | exact resolve eq2417 eq2370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2417
  have eq2455 : (M.op (σ x) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq2392 eq468
    | exact resolve eq468 eq2392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2463 : (σ x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq2392 eq2455
    | exact resolve eq2455 eq2392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2455
  have eq2498 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2422 eq155
    | exact resolve eq155 eq2422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq155
  have eq2543 : (σ x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq2498
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq2498
    | exact resolve eq2498 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq2498
  have eq2563 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq2463 eq566
    | exact resolve eq566 eq2463
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq566 eq2463
  have eq2569 : x = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq2422 eq2563
    | exact resolve eq2563 eq2422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2563
  have eq2671 : (M.op (M.op (σ x) (σ y)) x) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq2569 eq613
    | exact resolve eq613 eq2569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq613
  have eq2676 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op (σ x) (σ y)) x) := by
    first
    | exact superpose eq1672 eq2671
    | exact resolve eq2671 eq1672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2671
  have eq2683 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (M.op (M.op x y) (σ x)) := by
    first
    | exact superpose eq410 eq2676
    | exact resolve eq2676 eq410
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq410 eq2676
  have eq2685 : x = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq2569 eq2683
    | exact resolve eq2683 eq2569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2683
  have eq2686 : x = (σ x) := by
    first
    | exact superpose eq2543 eq2685
    | exact resolve eq2685 eq2543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2685
  have eq2688 : (M.op (σ x) (σ y)) = (M.op x (σ y)) := by
    first
    | exact superpose eq2686 eq26
    | exact resolve eq26 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq2689 : x = (τ x) := by
    first
    | exact superpose eq2686 eq28
    | exact resolve eq28 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq2790 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op (M.op (M.op x y) (σ x)) X0) := by
    intro X0
    first
    | exact superpose eq2392 eq246
    | exact resolve eq246 eq2392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2392
  have eq2883 : ∀ X0 : G, (M.op (M.op X0 X0) (σ x)) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq2569 eq2790
    | exact resolve eq2790 eq2569
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2569 eq2790
  have eq2919 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = (M.op x X0) := by
    intro X0
    first
    | exact superpose eq468 eq2883
    | exact resolve eq2883 eq468
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq468 eq2883
  have eq3488 : (M.op x (M.op x y)) = (M.op (M.op x (M.op x y)) x) := by
    first
    | exact superpose eq2337 eq53
    | exact resolve eq53 eq2337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq3539 : (M.op x (M.op x y)) = (M.op (M.op x x) x) := by
    first
    | (have i₁ := eq3488
       have i₂ := eq14 x x sF0
       grind)
    | exact superpose eq14 eq3488
    | exact resolve eq3488 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3488
  have eq3575 : (M.op (M.op x y) x) = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq3539
       have i₂ := eq467 x x
       grind)
    | exact superpose eq467 eq3539
    | exact resolve eq3539 eq467
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq467 eq3539
  have eq3594 : x = (M.op x (M.op x y)) := by
    first
    | exact superpose eq2370 eq3575
    | exact resolve eq3575 eq2370
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2370 eq3575
  have eq3803 : ∀ X0 X1 X2 : G, (M.op (M.op x X0) X1) = (M.op (M.op X1 X1) (M.op x X2)) := by
    intro X0 X1 X2
    first
    | exact superpose eq2337 eq804
    | exact resolve eq804 eq2337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq804
  have eq3804 : ∀ X1 X2 : G, (M.op (M.op x y) X1) = (M.op (M.op X1 X1) (M.op x X2)) := by
    intro X1 X2
    first
    | (have i₁ := eq3803 x X1 X2
       have i₂ := eq242 x X1
       grind)
    | (have i₁ := eq3803 y X1 X2
       have i₂ := eq242 x X1
       grind)
    | exact superpose eq242 eq3803
    | (have j0 := eq3803 y X1 X2
       grind)
    | exact resolve eq3803 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3803
  have eq3805 : ∀ X1 X2 : G, (M.op x X1) = (M.op (M.op X1 X1) (M.op x X2)) := by
    intro X1 X2
    first
    | exact superpose eq2337 eq3804
    | exact resolve eq3804 eq2337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3804
  have eq3938 : ∀ X0 X1 : G, (M.op x (M.op x X0)) = (M.op (M.op (M.op x y) (M.op x X0)) (M.op x X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3805 (M.op x X0) X1
       have i₂ := eq242 X0 (M.op x X0)
       grind)
    | (have i₁ := eq3805 (M.op x y) x
       have i₂ := eq242 X0 (M.op x y)
       grind)
    | exact superpose eq242 eq3805
    | exact resolve eq3805 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4010 : ∀ X0 X1 X2 : G, (M.op (M.op x x) (M.op X0 X1)) = (M.op (M.op (M.op X2 X2) X0) (M.op x x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq56 X2 X0 (M.op x x) X1
       have i₂ := eq3805 x x
       grind)
    | exact superpose eq3805 eq56
    | exact resolve eq56 eq3805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq4056 : ∀ X0 X1 X2 : G, (M.op (M.op x x) (M.op X0 X1)) = (M.op (M.op (M.op x y) X2) (M.op x x)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4010 X0 X1 X2
       have i₂ := eq456 X2 (M.op x x) X0
       grind)
    | exact superpose eq456 eq4010
    | exact resolve eq4010 eq456
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq456 eq4010
  have eq4115 : ∀ X0 X1 : G, (M.op x (M.op x X0)) = (M.op (M.op (M.op x y) (M.op x y)) (M.op x X1)) := by
    intro X0 X1
    first
    | exact superpose eq427 eq3938
    | exact resolve eq3938 eq427
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq427 eq3938
  have eq4139 : ∀ X0 X1 X2 : G, (M.op x (M.op X0 X1)) = (M.op (M.op (M.op x y) X2) x) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq4056 X0 X1 X2
       have i₂ := eq2318
       grind)
    | exact superpose eq2318 eq4056
    | exact resolve eq4056 eq2318
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2318 eq4056
  have eq4192 : ∀ X0 : G, (M.op x (M.op x y)) = (M.op x (M.op x X0)) := by
    intro X0
    first
    | (have i₁ := eq4115 X0 x
       have i₂ := eq3805 sF0 x
       grind)
    | exact superpose eq3805 eq4115
    | exact resolve eq4115 eq3805
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3805 eq4115
  have eq4213 : ∀ X0 X1 : G, (M.op (M.op x x) (M.op x y)) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4139 X0 X1 sF0
       have i₂ := eq14 sF0 x x
       grind)
    | (have i₁ := eq4139 X0 X1 x
       have i₂ := eq14 x sF0 x
       grind)
    | exact superpose eq14 eq4139
    | exact resolve eq4139 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4139
  have eq4254 : ∀ X0 : G, x = (M.op x (M.op x X0)) := by
    intro X0
    first
    | exact superpose eq3594 eq4192
    | exact resolve eq4192 eq3594
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3594 eq4192
  have eq4272 : ∀ X0 X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq4213 X0 X1
       have i₂ := eq242 x sF0
       grind)
    | exact superpose eq242 eq4213
    | exact resolve eq4213 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4213
  have eq4312 : ∀ X0 X1 : G, x = (M.op x (M.op X0 X1)) := by
    intro X0 X1
    first
    | exact superpose eq2422 eq4272
    | exact resolve eq4272 eq2422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2422 eq4272
  have eq4403 : ∀ X1 : G, (M.op x X1) ≠ (M.op (M.op X1 X1) (M.op X1 X1)) ∨ (M.op x X1) = (k x (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq69 x (M.op x x) x
       have i₂ := eq4254 x
       grind)
    | exact superpose eq4254 eq69
    | exact resolve eq69 eq4254
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69 eq4254
  have eq4421 : ∀ X1 : G, (M.op x X1) ≠ (M.op (M.op (M.op x y) X1) X1) ∨ (M.op x X1) = (k x (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq4403 X1
       have i₂ := eq246 X1 X1
       grind)
    | exact superpose eq246 eq4403
    | (have j0 := eq4403 X1
       grind)
    | exact resolve eq4403 eq246
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq246 eq4403
  have eq4438 : ∀ X1 : G, (M.op x X1) ≠ (M.op (M.op x X1) X1) ∨ (M.op x X1) = (k x (M.op X1 X1)) := by
    intro X1
    first
    | exact superpose eq2337 eq4421
    | (have j0 := eq4421 X1
       grind)
    | exact resolve eq4421 eq2337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4421
  have eq4446 : ∀ X1 : G, (M.op (M.op x y) X1) ≠ (M.op x X1) ∨ (M.op x X1) = (k x (M.op X1 X1)) := by
    intro X1
    first
    | (have i₁ := eq4438 X1
       have i₂ := eq242 X1 X1
       grind)
    | (have i₁ := eq4438 y
       have i₂ := eq242 x y
       grind)
    | exact superpose eq242 eq4438
    | (have j0 := eq4438 X1
       grind)
    | exact resolve eq4438 eq242
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq242 eq4438
  have eq4451 : ∀ X1 : G, (M.op x X1) = (k x (M.op X1 X1)) := by
    intro X1
    first
    | (have j0 := eq4446 X1
       grind)
    | (have r₁ := eq4446 x
       have r₂ := eq2337 x
       grind)
    | exact resolve eq4446 eq2337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2337 eq4446
  have eq4478 : ∀ X0 : G, x = (M.op x (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq4312 (σ X0) (σ X0)
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq4312
    | exact resolve eq4312 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq4312
  have eq6773 : ∀ X0 : G, (M.op x X0) = (k X0 (M.op (σ x) (σ y))) ∨ (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq2919 eq1403
    | (have j0 := eq1403 X0
       grind)
    | exact resolve eq1403 eq2919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1403
  have eq6774 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) ≠ (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ (M.op x X0) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq1672 eq6773
    | (have j0 := eq6773 X0
       grind)
    | exact resolve eq6773 eq1672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1672 eq6773
  have eq6775 : ∀ X0 : G, (σ x) ≠ (M.op (M.op (σ x) (σ y)) X0) ∨ (M.op x X0) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2543 eq6774
    | (have j0 := eq6774 X0
       grind)
    | exact resolve eq6774 eq2543
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2543 eq6774
  have eq6776 : ∀ X0 : G, (σ x) ≠ (M.op x X0) ∨ (M.op x X0) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2919 eq6775
    | (have j0 := eq6775 X0
       grind)
    | exact resolve eq6775 eq2919
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2919 eq6775
  have eq6777 : ∀ X0 : G, x ≠ (M.op x X0) ∨ (M.op x X0) = (k X0 (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2686 eq6776
    | (have j0 := eq6776 X0
       grind)
    | exact resolve eq6776 eq2686
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2686 eq6776
  have eq6783 : ∀ X0 : G, x ≠ x ∨ x = (k (σ (M.op X0 X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have i₁ := eq6777 (σ (M.op X0 X0))
       have i₂ := eq4478 X0
       grind)
    | exact superpose eq4478 eq6777
    | (have r₁ := eq6777 (σ (M.op X0 X0))
       have r₂ := eq4478 X0
       grind)
    | exact resolve eq6777 eq4478
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4478 eq6777
  have eq6798 : ∀ X0 : G, x = (k (σ (M.op X0 X0)) (M.op (σ x) (σ y))) := by
    intro X0
    first
    | (have j0 := eq6783 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6783
  have eq6892 : ∀ X0 : G, (τ x) = (k (M.op X0 X0) (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | exact superpose eq6798 eq395
    | exact resolve eq395 eq6798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq395
  have eq6895 : ∀ X0 : G, x = (k (M.op X0 X0) (τ (M.op (σ x) (σ y)))) := by
    intro X0
    first
    | (have i₁ := eq6892 X0
       have i₂ := eq2689
       grind)
    | exact superpose eq2689 eq6892
    | exact resolve eq6892 eq2689
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2689 eq6892
  have eq7707 : ∀ X0 X1 : G, (k x (σ X1)) = (σ (k (k (M.op X0 X0) (τ (M.op (σ x) (σ y)))) X1)) := by
    intro X0 X1
    first
    | exact superpose eq6798 eq393
    | exact resolve eq393 eq6798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq393 eq6798
  have eq7769 : ∀ X1 : G, (k x (σ X1)) = (σ (k x X1)) := by
    intro X1
    first
    | exact superpose eq6895 eq7707
    | exact resolve eq7707 eq6895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6895 eq7707
  have eq10034 : (σ (k x (M.op y y))) = (k x (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq7769 (M.op y y)
       have i₂ := eq100
       grind)
    | exact superpose eq100 eq7769
    | exact resolve eq7769 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100 eq7769
  have eq10087 : (σ (k x (M.op y y))) = (M.op x (σ y)) := by
    first
    | (have i₁ := eq10034
       have i₂ := eq4451 sF3
       grind)
    | exact superpose eq4451 eq10034
    | exact resolve eq10034 eq4451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10034
  have eq10097 : (M.op (σ x) (σ y)) = (σ (k x (M.op y y))) := by
    first
    | exact superpose eq2688 eq10087
    | exact resolve eq10087 eq2688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2688 eq10087
  have eq10107 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10097
       have i₂ := eq4451 y
       grind)
    | exact superpose eq4451 eq10097
    | exact resolve eq10097 eq4451
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4451 eq10097
  have eq10114 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10107
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq10107
    | exact resolve eq10107 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq10107
  have eq10121 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq20 eq10114
    | exact resolve eq10114 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq10114
  have eq10127 : False := by grind
  exact eq10127

/-- `Equation4629`: `(x ◇ y) ◇ x = (x ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(Y,Y) else if m(Y,X) = m(Y,Y) then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_pyx_pyy_pyy_pxx_pyx_Equation4629 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4629 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4629.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a ≠ M.op b b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ M.op b a = M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X1) := by
    intro X0 X1
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
  have eq68 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq70 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 X0 X0
       have i₂ := eq68 (σ X0)
       grind)
    | exact superpose eq68 eq10
    | exact resolve eq10 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : (k (σ x) (σ x)) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq43
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq43
    | exact resolve eq43 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq43
  have eq72 : (σ (M.op x x)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq71
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq71
    | exact resolve eq71 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq73 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq70 X0
       have i₂ := eq68 X0
       grind)
    | exact superpose eq68 eq70
    | exact resolve eq70 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq70
  have eq79 : (k x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq49
       have i₂ := eq68 sF2
       grind)
    | exact superpose eq68 eq49
    | exact resolve eq49 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq49
  have eq80 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
    first
    | (have i₁ := eq79
       have i₂ := eq68 x
       grind)
    | exact superpose eq68 eq79
    | exact resolve eq79 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq81 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X1) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
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
  have eq95 : (M.op x y) ≠ (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (k y x) := by
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
  have eq96 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq12
    | (have j0 := eq12 (σ y) (σ x)
       grind)
    | exact resolve eq12 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (k (σ y) (σ x)) = (σ (k y x)) := by
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
  have eq105 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq109 : (M.op (σ y) (σ y)) = (σ (k y y)) := by
    first
    | (have i₁ := eq105
       have i₂ := eq68 sF3
       grind)
    | exact superpose eq68 eq105
    | exact resolve eq105 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq111 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq109
       have i₂ := eq68 y
       grind)
    | exact superpose eq68 eq109
    | exact resolve eq109 eq68
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq109
  have eq127 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq104
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq104 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq133 : (k y x) = (τ (k (σ y) (σ x))) := by
    first
    | (have i₁ := eq16 (k y x)
       have i₂ := eq104
       grind)
    | exact superpose eq104 eq16
    | exact resolve eq16 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq134 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq127
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq127
    | exact resolve eq127 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq127
  have eq135 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq20 eq134
    | exact resolve eq134 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq134
  have eq136 : (M.op x y) = (M.op x x) ∨ (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq135
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq135
    | exact resolve eq135 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq137 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq136
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq136
    | exact resolve eq136 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq153 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq111
       grind)
    | exact superpose eq111 eq16
    | exact resolve eq16 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq789 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq81 X0 X1
       have i₂ := eq73 X1
       grind)
    | exact superpose eq73 eq81
    | (have j0 := eq81 X0 X1
       grind)
    | exact resolve eq81 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq81
  have eq790 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X1) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq789 X0 X1
       have i₂ := eq73 X0
       grind)
    | exact superpose eq73 eq789
    | (have j0 := eq789 X0 X1
       grind)
    | exact resolve eq789 eq73
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73 eq789
  have eq861 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (k X1 X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq790 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq862 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq790 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq790
  have eq25787 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq137 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq137
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25797 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq25787
    | exact resolve eq25787 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25787
  have eq25808 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq25797
       have r₂ := eq27
       grind)
    | exact resolve eq25797 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25797
  have eq25812 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq25808
    | exact resolve eq25808 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25808
  have eq25814 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq25812
    | exact resolve eq25812 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25812
  have eq26158 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k (σ y) X0) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq25814 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq25814
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq25814
       grind)
    | exact resolve eq13 eq25814
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25814
  have eq30893 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq26158
    | (have j0 := eq26158 (σ x)
       grind)
    | (have r₁ := eq26158 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq26158 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26158
  have eq30898 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq30893
  have eq30991 : (τ (M.op (σ x) (σ x))) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq30898 eq133
    | exact resolve eq133 eq30898
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30898
  have eq31023 : (M.op x x) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq80 eq30991
    | exact resolve eq30991 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq30991
  have eq31300 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq31023
       grind)
    | exact superpose eq31023 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq31023
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31023
  have eq31309 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq31300
  have eq31318 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq31309
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31309
    | exact resolve eq31309 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31309
  have eq31319 : (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq31318
  have eq31339 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq31319
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq31319
    | exact resolve eq31319 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31319
  have eq31340 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq31339
  have eq31413 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq31340 eq96
    | (have r₁ := eq96
       have r₂ := eq31340
       grind)
    | exact resolve eq96 eq31340
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq31446 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq31413
  have eq40605 : (k y x) = (τ (M.op (σ y) (σ y))) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq31446 eq133
    | exact resolve eq133 eq31446
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq133 eq31446
  have eq40645 : (M.op y y) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq153 eq40605
    | exact resolve eq40605 eq153
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq153 eq40605
  have eq40651 : (M.op y y) = (k y x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq40645
       have r₂ := eq95
       grind)
    | exact resolve eq40645 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40645
  have eq40666 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq40651
       grind)
    | exact superpose eq40651 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq40651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40651
  have eq40675 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq40666
  have eq40686 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq40675
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq40675
    | exact resolve eq40675 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40675
  have eq40687 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq40686
  have eq40707 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq40687
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq40687
    | exact resolve eq40687 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40687
  have eq41088 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k (σ y) X0) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | exact superpose eq40707 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq40707
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq40707
       grind)
    | exact resolve eq13 eq40707
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40707
  have eq69189 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq41088
    | (have j0 := eq41088 (σ x)
       grind)
    | (have r₁ := eq41088 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq41088 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41088
  have eq69200 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq69189
  have eq69214 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq69200 eq137
    | exact resolve eq137 eq69200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137 eq69200
  have eq69252 : (σ (M.op x y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq69214
  have eq69281 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq69252 eq31340
    | exact resolve eq31340 eq69252
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31340 eq69252
  have eq69362 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq69281
  have eq69376 : (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq69362
       have r₂ := eq27
       grind)
    | exact resolve eq69362 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69362
  have eq69401 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq111
       have i₂ := eq69376
       grind)
    | exact superpose eq69376 eq111
    | exact resolve eq111 eq69376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69412 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) ∨ (M.op x y) = (M.op x x) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq69376
       grind)
    | exact superpose eq69376 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq69376
       grind)
    | exact resolve eq13 eq69376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69376
  have eq69457 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq20 eq69401
    | exact resolve eq69401 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69401
  have eq85890 : (M.op x y) ≠ (M.op x y) ∨ (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq69412 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq69412
    | (have j0 := eq69412 x
       grind)
    | (have r₁ := eq69412 x
       have r₂ := eq18
       grind)
    | exact resolve eq69412 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69412
  have eq85900 : (M.op x x) = (k y x) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq85890
  have eq85904 : (σ (M.op x x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq104
       have i₂ := eq85900
       grind)
    | exact superpose eq85900 eq104
    | exact resolve eq104 eq85900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85927 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq861 x y
       have i₂ := eq85900
       grind)
    | exact superpose eq85900 eq861
    | (have j0 := eq861 x y
       grind)
    | exact resolve eq861 eq85900
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861 eq85900
  have eq85931 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq85927
  have eq85937 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq85931
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq85931
    | exact resolve eq85931 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85931
  have eq85954 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq85904
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq85904
    | exact resolve eq85904 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85904
  have eq85960 : (M.op (σ x) (σ x)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq85937
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq85937
    | exact resolve eq85937 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85937
  have eq85969 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq85960
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq85960
    | exact resolve eq85960 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85960
  have eq85976 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq85969
    | exact resolve eq85969 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85969
  have eq85983 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq85976
       have i₂ := eq111
       grind)
    | exact superpose eq111 eq85976
    | exact resolve eq85976 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85976
  have eq85990 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq85983
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq85983
    | exact resolve eq85983 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85983
  have eq85997 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq85990
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq85990
    | exact resolve eq85990 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85990
  have eq86004 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq26 eq85997
    | exact resolve eq85997 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85997
  have eq86445 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq86004 eq69457
    | exact resolve eq69457 eq86004
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86004
  have eq86510 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by grind
  clear eq86445
  have eq86534 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq86510
       have r₂ := eq27
       grind)
    | exact resolve eq86510 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86510
  have eq86562 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq86534 eq96
    | (have r₁ := eq96
       have r₂ := eq86534
       grind)
    | exact resolve eq96 eq86534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq86610 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq86562
  have eq105853 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq86610 eq85954
    | exact resolve eq85954 eq86610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85954 eq86610
  have eq105864 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq105853
  have eq106878 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op x x) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by grind
  clear eq105864
  have eq106961 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq106878
       have r₂ := eq86534
       grind)
    | exact resolve eq106878 eq86534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86534 eq106878
  have eq106996 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | exact superpose eq106961 eq69457
    | exact resolve eq69457 eq106961
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq69457 eq106961
  have eq107065 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op x x) := by grind
  clear eq106996
  have eq107091 : (M.op x y) = (M.op x x) := by
    first
    | (have r₁ := eq107065
       have r₂ := eq27
       grind)
    | exact resolve eq107065 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107065
  have eq107120 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq72
       have i₂ := eq107091
       grind)
    | exact superpose eq107091 eq72
    | exact resolve eq72 eq107091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107121 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (M.op y y) = (k y x) := by
    first
    | (have i₁ := eq95
       have i₂ := eq107091
       grind)
    | exact superpose eq107091 eq95
    | (have r₁ := eq95
       have r₂ := eq107091
       grind)
    | exact resolve eq95 eq107091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq107159 : (M.op y y) = (k y x) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq107121
  have eq107174 : (σ (M.op x y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq20 eq107120
    | exact resolve eq107120 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107120
  have eq111849 : (k (σ y) (σ x)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq104
       have i₂ := eq107159
       grind)
    | exact superpose eq107159 eq104
    | exact resolve eq104 eq107159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq111876 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq862 x y
       have i₂ := eq107159
       grind)
    | exact superpose eq107159 eq862
    | (have j0 := eq862 x y
       grind)
    | exact resolve eq862 eq107159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107159
  have eq111879 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq111876
  have eq111886 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq111879
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq111879
    | exact resolve eq111879 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111879
  have eq111906 : (M.op (σ y) (σ y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq111849
       have i₂ := eq111
       grind)
    | exact superpose eq111 eq111849
    | exact resolve eq111849 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111849
  have eq111911 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq107174 eq111886
    | exact resolve eq111886 eq107174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111886
  have eq111920 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq111911
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq111911
    | exact resolve eq111911 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111911
  have eq111927 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq111920
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq111920
    | exact resolve eq111920 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111920
  have eq111934 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq111927
    | exact resolve eq111927 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111927
  have eq111941 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq111934
       have r₂ := eq27
       grind)
    | exact resolve eq111934 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111934
  have eq111948 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq111941
       have i₂ := eq111
       grind)
    | exact superpose eq111 eq111941
    | exact resolve eq111941 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111941
  have eq111955 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq111948
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq111948
    | exact resolve eq111948 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111948
  have eq111962 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq111955
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq111955
    | exact resolve eq111955 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111955
  have eq111969 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq111962
    | exact resolve eq111962 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111962
  have eq112042 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (M.op X0 X0) = (k (σ y) X0) ∨ (M.op x y) = (M.op y y) := by
    intro X0
    first
    | exact superpose eq111969 eq13
    | (have j0 := eq13 (σ y) X0
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq111969
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq111969
       grind)
    | exact resolve eq13 eq111969
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148072 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq26 eq112042
    | (have j0 := eq112042 (σ x)
       grind)
    | (have r₁ := eq112042 (σ x)
       have r₂ := eq26
       grind)
    | exact resolve eq112042 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112042
  have eq148092 : (M.op (σ x) (σ x)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq148072
  have eq148095 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq107174 eq148092
    | exact resolve eq148092 eq107174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148092
  have eq148145 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq148095 eq111906
    | exact resolve eq111906 eq148095
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111906 eq148095
  have eq148154 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq148145
  have eq148310 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | exact superpose eq148154 eq111969
    | exact resolve eq111969 eq148154
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111969 eq148154
  have eq148387 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq148310
  have eq148476 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq148387
       have r₂ := eq27
       grind)
    | exact resolve eq148387 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148387
  have eq148554 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq111
       have i₂ := eq148476
       grind)
    | exact superpose eq148476 eq111
    | exact resolve eq111 eq148476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148575 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op X0 X0) = (k y X0) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq148476
       grind)
    | exact superpose eq148476 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq148476
       grind)
    | exact resolve eq13 eq148476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148476
  have eq148623 : (σ (M.op x y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq20 eq148554
    | exact resolve eq148554 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148554
  have eq148861 : (M.op x y) ≠ (M.op x y) ∨ (M.op x x) = (k y x) := by
    first
    | (have i₁ := eq148575 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq148575
    | (have j0 := eq148575 x
       grind)
    | (have r₁ := eq148575 x
       have r₂ := eq18
       grind)
    | exact resolve eq148575 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq148575
  have eq148871 : (M.op x x) = (k y x) := by grind
  clear eq148861
  have eq148873 : (M.op x y) = (k y x) := by
    first
    | (have i₁ := eq148871
       have i₂ := eq107091
       grind)
    | exact superpose eq107091 eq148871
    | exact resolve eq148871 eq107091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107091 eq148871
  have eq148920 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq862 x y
       have i₂ := eq148873
       grind)
    | exact superpose eq148873 eq862
    | (have j0 := eq862 x y
       grind)
    | exact resolve eq862 eq148873
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq862 eq148873
  have eq148933 : (σ (M.op x y)) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq148920
       have i₂ := eq111
       grind)
    | exact superpose eq111 eq148920
    | exact resolve eq148920 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148920
  have eq148954 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq148623 eq148933
    | (have r₁ := eq148933
       have r₂ := eq148623
       grind)
    | exact resolve eq148933 eq148623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148933
  have eq148963 : (M.op (σ x) (σ y)) = (σ (M.op x x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq148954
       have r₂ := eq20
       grind)
    | exact resolve eq148954 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq148954
  have eq148970 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq148963
       have i₂ := eq72
       grind)
    | exact superpose eq72 eq148963
    | exact resolve eq148963 eq72
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq148963
  have eq148977 : (M.op (σ x) (σ y)) = (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq107174 eq148970
    | exact resolve eq148970 eq107174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107174 eq148970
  have eq148984 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq148977
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq148977
    | exact resolve eq148977 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148977
  have eq148991 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq148984
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq148984
    | exact resolve eq148984 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148984
  have eq148998 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | exact superpose eq26 eq148991
    | exact resolve eq148991 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148991
  have eq149005 : (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq148998
       have r₂ := eq27
       grind)
    | exact resolve eq148998 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148998
  have eq149012 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq149005
       have i₂ := eq111
       grind)
    | exact superpose eq111 eq149005
    | exact resolve eq149005 eq111
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq111 eq149005
  have eq149019 : (M.op (σ x) (σ y)) = (σ (M.op x y)) := by
    first
    | exact superpose eq148623 eq149012
    | exact resolve eq149012 eq148623
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148623 eq149012
  have eq149026 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq149019
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq149019
    | exact resolve eq149019 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq149019
  have eq149033 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq149026
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq149026
    | exact resolve eq149026 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq149026
  have eq149040 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq149033
    | exact resolve eq149033 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq149033
  have eq149047 : False := by grind
  exact eq149047

/-- `Equation4646`: `(x ◇ y) ◇ x = (z ◇ y) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,X) else if m(Y,X) = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyx_y_pxx_pxx_pyx_Equation4646 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law4646 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law4646.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) = X1 ∨ (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op X2 X1) X1) := by
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
  have eq28 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X1 ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq12 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | (have r₁ := eq12 X0 (M.op X0 X0)
       have r₂ := eq13 X0 (M.op X0 X0)
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 (k X0 X1)
       grind)
    | exact resolve eq12 eq13
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
  have eq35 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (k X0 (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (τ X0) X1
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq36 : ∀ X0 : G, (σ (k x X0)) = (k (σ x) (σ X0)) := by
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
  have eq37 : ∀ X0 : G, (σ (k y X0)) = (k (σ y) (σ X0)) := by
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
  have eq38 : ∀ X0 : G, (σ (k (M.op x y) X0)) = (k (σ (M.op x y)) (σ X0)) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 (M.op x y) X0
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq39 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (k (σ X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq10 X1 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq42 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq45 : ∀ X0 : G, (k x X0) = (τ (k (σ x) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k x X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36
  have eq48 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq37 X0
       grind)
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq98 : (k x x) = (τ (k (σ x) (σ x))) := by
    first
    | (have i₁ := eq45 x
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq45
    | (have j0 := eq45 x
       grind)
    | exact resolve eq45 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45
  have eq116 : (k y y) = (τ (k (σ y) (σ y))) := by
    first
    | (have i₁ := eq48 y
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq48
    | (have j0 := eq48 y
       grind)
    | exact resolve eq48 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48
  have eq175 : ∀ X0 : G, (M.op (M.op X0 y) y) = (M.op (M.op x y) x) := by
    intro X0
    first
    | (have i₁ := eq16 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 x y X0
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq176 : ∀ X0 : G, (M.op (M.op X0 (σ y)) (σ y)) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 (σ x) (σ y) X0
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op (M.op X0 y) X0) = (M.op (M.op x y) y) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq16
    | (have j0 := eq16 X0 y x
       grind)
    | exact resolve eq16 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182 : ∀ X0 : G, (M.op (M.op X0 (σ y)) X0) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    intro X0
    first
    | exact superpose eq26 eq16
    | (have j0 := eq16 X0 (σ y) (σ x)
       grind)
    | exact resolve eq16 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq187 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op X0 X0)) := by
    intro X0
    first
    | (have j0 := eq13 X0 (M.op X0 X0)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq188 : (M.op (M.op x y) x) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq175 x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq175
    | (have j0 := eq175 x
       grind)
    | exact resolve eq175 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) y) := by
    first
    | (have i₁ := eq175 (M.op x y)
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq175
    | exact resolve eq175 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq195 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op X0 y) X0) := by
    intro X0
    first
    | (have i₁ := eq16 X0 y x
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq197 : ∀ X0 X1 : G, (M.op (M.op X1 y) y) = (M.op (M.op (M.op x y) x) (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 y) y X1
       have i₂ := eq175 X0
       grind)
    | exact superpose eq175 eq16
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq198 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (M.op X0 y)) := by
    intro X0
    first
    | (have i₁ := eq197 X0 x
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq197
    | exact resolve eq197 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq197
  have eq204 : ∀ X0 : G, (M.op (M.op X0 y) y) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    intro X0
    first
    | exact superpose eq188 eq16
    | exact resolve eq16 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq205 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (M.op x y)) := by
    first
    | (have i₁ := eq204 x
       have i₂ := eq175 x
       grind)
    | exact superpose eq175 eq204
    | exact resolve eq204 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq204
  have eq209 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (σ y)) := by
    first
    | exact superpose eq176 eq176
    | exact resolve eq176 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq26 eq176
    | (have j0 := eq176 (σ x)
       grind)
    | exact resolve eq176 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq216 : ∀ X0 X1 : G, (M.op (M.op X1 (σ y)) (σ y)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (σ y))) := by
    intro X0 X1
    first
    | exact superpose eq176 eq16
    | exact resolve eq16 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq217 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op X0 (σ y))) := by
    intro X0
    first
    | exact superpose eq176 eq216
    | exact resolve eq216 eq176
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq176 eq216
  have eq239 : ∀ X0 X1 : G, (M.op (M.op X1 X0) X0) = (M.op (M.op (M.op x y) y) (M.op X0 y)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 (M.op X0 y) X0 X1
       have i₂ := eq181 X0
       grind)
    | exact superpose eq181 eq16
    | exact resolve eq16 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq243 : ∀ X0 X1 : G, (M.op (M.op (M.op x y) x) (M.op X0 y)) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq188 eq239
    | exact resolve eq239 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq239
  have eq251 : ∀ X0 X1 : G, (M.op (M.op x y) x) = (M.op (M.op X1 X0) X0) := by
    intro X0 X1
    first
    | exact superpose eq198 eq243
    | exact resolve eq243 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq243
  have eq255 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op x y) y) (M.op (σ y) y)) := by
    first
    | (have i₁ := eq182 (M.op sF3 y)
       have i₂ := eq181 sF3
       grind)
    | exact superpose eq181 eq182
    | exact resolve eq182 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq266 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq182 eq16
    | exact resolve eq16 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq268 : (M.op (M.op x y) y) = (M.op (M.op (M.op (σ x) (σ y)) (σ y)) (M.op y (σ y))) := by
    first
    | exact superpose eq182 eq181
    | exact resolve eq181 eq182
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq272 : (M.op (M.op x y) y) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) (M.op y (σ y))) := by
    first
    | exact superpose eq210 eq268
    | exact resolve eq268 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq268
  have eq274 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op (σ x) (σ y)) (σ x)) X1) := by
    intro X0 X1
    first
    | exact superpose eq210 eq266
    | exact resolve eq266 eq210
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210 eq266
  have eq279 : (M.op (M.op (σ x) (σ y)) (σ y)) = (M.op (M.op (M.op x y) x) (M.op (σ y) y)) := by
    first
    | exact superpose eq188 eq255
    | exact resolve eq255 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq255
  have eq282 : (M.op (M.op (σ x) (σ y)) (σ x)) = (M.op (M.op x y) y) := by
    first
    | exact superpose eq217 eq272
    | exact resolve eq272 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq217 eq272
  have eq284 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (σ y)) := by
    first
    | exact superpose eq198 eq279
    | exact resolve eq279 eq198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq198 eq279
  have eq287 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (σ x)) := by
    first
    | exact superpose eq188 eq282
    | exact resolve eq282 eq188
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq188 eq282
  have eq335 : (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) (σ y)) := by
    first
    | exact superpose eq287 eq209
    | exact resolve eq209 eq287
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq209
  have eq392 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op x y) x) X0) := by
    intro X0
    first
    | (have i₁ := eq251 X0 (M.op X0 y)
       have i₂ := eq195 X0
       grind)
    | (have i₁ := eq251 x (M.op x y)
       have i₂ := eq195 X0
       grind)
    | exact superpose eq195 eq251
    | exact resolve eq251 eq195
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq195
  have eq413 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op x y) x) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq251 X1 x
       grind)
    | exact superpose eq251 eq16
    | exact resolve eq16 eq251
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq580 : (M.op (M.op x y) x) = (k (M.op (M.op x y) x) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq392 eq187
    | exact resolve eq187 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq187
  have eq608 : ∀ X0 : G, (M.op (M.op x y) x) ≠ (M.op (M.op x y) x) ∨ (M.op X0 X0) = (k X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | exact superpose eq392 eq28
    | (have j0 := eq28 X0 (M.op (M.op x y) x)
       grind)
    | (have r₁ := eq28 X0 (M.op (M.op x y) x)
       have r₂ := eq392 X0
       grind)
    | exact resolve eq28 eq392
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq609 : (M.op (M.op x y) x) ≠ (M.op (M.op x y) x) ∨ (M.op y y) = (k y (M.op (M.op x y) x)) := by
    first
    | exact superpose eq191 eq28
    | (have j0 := eq28 y (M.op (M.op x y) x)
       grind)
    | (have r₁ := eq28 y (M.op (M.op x y) x)
       have r₂ := eq191
       grind)
    | exact resolve eq28 eq191
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq610 : (M.op (M.op x y) x) ≠ (M.op (M.op x y) x) ∨ (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq205 eq28
    | (have j0 := eq28 (M.op x y) (M.op (M.op x y) x)
       grind)
    | (have r₁ := eq28 (M.op x y) (M.op (M.op x y) x)
       have r₂ := eq205
       grind)
    | exact resolve eq28 eq205
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205
  have eq612 : (M.op (M.op x y) x) ≠ (M.op (M.op x y) x) ∨ (M.op (σ y) (σ y)) = (k (σ y) (M.op (M.op x y) x)) := by
    first
    | exact superpose eq335 eq28
    | (have j0 := eq28 (σ y) (M.op (M.op x y) x)
       grind)
    | (have r₁ := eq28 (σ y) (M.op (M.op x y) x)
       have r₂ := eq335
       grind)
    | exact resolve eq28 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq627 : (M.op (σ y) (σ y)) = (k (σ y) (M.op (M.op x y) x)) := by grind
  clear eq612
  have eq629 : (M.op (M.op x y) (M.op x y)) = (k (M.op x y) (M.op (M.op x y) x)) := by grind
  clear eq610
  have eq630 : (M.op y y) = (k y (M.op (M.op x y) x)) := by grind
  clear eq609
  have eq631 : ∀ X0 : G, (M.op X0 X0) = (k X0 (M.op (M.op x y) x)) := by
    intro X0
    first
    | (have j0 := eq608 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq608
  have eq656 : (M.op x y) = (k y x) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq11 y x
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq11
    | (have j0 := eq11 y x
       grind)
    | exact resolve eq11 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq658 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq860 : ∀ X0 : G, (k X0 (M.op (M.op x y) x)) = (k X0 X0) ∨ (k X0 (M.op (M.op x y) x)) = X0 ∨ (k X0 (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | (have i₁ := eq11 X0 X0
       have i₂ := eq631 X0
       grind)
    | exact superpose eq631 eq11
    | exact resolve eq11 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq861 : ∀ X0 : G, (k X0 (M.op (M.op x y) x)) ≠ X0 ∨ (k X0 (M.op (M.op x y) x)) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq28 X0 X0
       have i₂ := eq631 X0
       grind)
    | exact superpose eq631 eq28
    | exact resolve eq28 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28
  have eq872 : ∀ X0 : G, (k X0 (M.op (M.op x y) x)) = (k X0 X0) ∨ (k X0 (M.op (M.op x y) x)) = X0 := by
    intro X0
    first
    | (have j0 := eq860 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq876 : ∀ X0 : G, (k X0 (M.op (M.op x y) x)) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq872 X0
       have j1 := eq861 X0
       grind)
    | (have r₁ := eq872 X0
       have r₂ := eq861 X0
       grind)
    | exact resolve eq872 eq861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861 eq872
  have eq885 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have i₁ := eq631 (M.op sF0 x)
       have i₂ := eq876 (M.op sF0 x)
       grind)
    | exact superpose eq876 eq631
    | exact resolve eq631 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq887 : (k y y) = (M.op y y) := by
    first
    | exact superpose eq876 eq630
    | exact resolve eq630 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq630
  have eq889 : (k (M.op x y) (M.op x y)) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq876 eq629
    | exact resolve eq629 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq629
  have eq894 : (k (σ y) (σ y)) = (M.op (σ y) (σ y)) := by
    first
    | exact superpose eq876 eq627
    | exact resolve eq627 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq627
  have eq914 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (k X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq251 X0 X0
       have i₂ := eq885 X0
       grind)
    | exact superpose eq885 eq251
    | exact resolve eq251 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq251
  have eq1000 : ∀ X0 : G, (M.op (M.op x y) x) = (M.op (σ (k X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq914 (σ X0)
       have i₂ := eq10 X0 X0
       grind)
    | exact superpose eq10 eq914
    | exact resolve eq914 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1070 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k (τ X0) X1)
       have i₂ := eq35 X0 X1
       grind)
    | exact superpose eq35 eq15
    | exact resolve eq15 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35
  have eq1140 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (k X0 (τ X1))
       have i₂ := eq39 X1 X0
       grind)
    | exact superpose eq39 eq15
    | exact resolve eq15 eq39
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq1186 : ∀ X0 : G, (k (τ (σ X0)) X0) = (τ (k (σ X0) (M.op (M.op x y) x))) := by
    intro X0
    first
    | (have i₁ := eq1070 (σ X0) X0
       have i₂ := eq876 (σ X0)
       grind)
    | exact superpose eq876 eq1070
    | exact resolve eq1070 eq876
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq876 eq1070
  have eq1210 : ∀ X0 : G, (k (τ (σ X0)) X0) = (k X0 (τ (M.op (M.op x y) x))) := by
    intro X0
    first
    | (have i₁ := eq1186 X0
       have i₂ := eq1140 X0 (M.op sF0 x)
       grind)
    | exact superpose eq1140 eq1186
    | exact resolve eq1186 eq1140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1186
  have eq1214 : ∀ X0 : G, (k X0 X0) = (k X0 (τ (M.op (M.op x y) x))) := by
    intro X0
    first
    | (have i₁ := eq1210 X0
       have i₂ := eq15 X0
       grind)
    | exact superpose eq15 eq1210
    | exact resolve eq1210 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1210
  have eq5568 : (M.op (M.op x y) x) = (M.op (σ (M.op (M.op x y) x)) (σ (M.op (M.op x y) x))) := by
    first
    | exact superpose eq580 eq1000
    | exact resolve eq1000 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5656 : (M.op (M.op x y) x) = (k (σ (M.op (M.op x y) x)) (M.op (M.op x y) x)) := by
    first
    | (have i₁ := eq5568
       have i₂ := eq631 (σ (M.op sF0 x))
       grind)
    | exact superpose eq631 eq5568
    | exact resolve eq5568 eq631
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq631 eq5568
  have eq6526 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq40 y
       have i₂ := eq656
       grind)
    | exact superpose eq656 eq40
    | exact resolve eq40 eq656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40 eq656
  have eq6528 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq6526
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq6526
    | exact resolve eq6526 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6526
  have eq6530 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ x = (M.op y y) := by
    first
    | exact superpose eq20 eq6528
    | exact resolve eq6528 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6528
  have eq6532 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6530
       have i₂ := eq887
       grind)
    | exact superpose eq887 eq6530
    | exact resolve eq6530 eq887
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq887 eq6530
  have eq6657 : (τ (M.op (M.op x y) x)) = (k (M.op (M.op x y) x) (τ (M.op (M.op x y) x))) := by
    first
    | exact superpose eq5656 eq1140
    | exact resolve eq1140 eq5656
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1140 eq5656
  have eq6664 : (k (M.op (M.op x y) x) (M.op (M.op x y) x)) = (τ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq1214 eq6657
    | exact resolve eq6657 eq1214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1214 eq6657
  have eq6667 : (M.op (M.op x y) x) = (τ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq580 eq6664
    | exact resolve eq6664 eq580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq580 eq6664
  have eq6687 : (M.op (M.op x y) x) = (σ (M.op (M.op x y) x)) := by
    first
    | exact superpose eq6667 eq14
    | exact resolve eq14 eq6667
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7053 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6532 eq658
    | exact resolve eq658 eq6532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq658 eq6532
  have eq7062 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq7053
       have r₂ := eq27
       grind)
    | exact resolve eq7053 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7053
  have eq7066 : (σ x) = (k (σ y) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq894 eq7062
    | exact resolve eq7062 eq894
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq894 eq7062
  have eq7068 : (τ (σ x)) = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7066 eq116
    | exact resolve eq116 eq7066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq116 eq7066
  have eq7084 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (k y y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq7068
    | exact resolve eq7068 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7068
  have eq7085 : x = (k y y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq7084
  have eq7098 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq914 y
       have i₂ := eq7085
       grind)
    | exact superpose eq7085 eq914
    | exact resolve eq914 eq7085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq914
  have eq7099 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq1000 y
       have i₂ := eq7085
       grind)
    | exact superpose eq7085 eq1000
    | exact resolve eq1000 eq7085
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7085
  have eq7103 : (M.op (M.op x y) x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7099
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq7099
    | exact resolve eq7099 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24 eq7099
  have eq7104 : (M.op x y) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7098
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq7098
    | exact resolve eq7098 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7098
  have eq7109 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq7103
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq7103
    | exact resolve eq7103 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7103
  have eq7113 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq7109
    | exact resolve eq7109 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7109
  have eq7114 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7104 eq7113
    | exact resolve eq7113 eq7104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7113
  have eq7123 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7114 eq284
    | exact resolve eq284 eq7114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq7129 : (M.op x y) ≠ (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  have eq7133 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq7123
    | exact resolve eq7123 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7123
  have eq7141 : (σ x) = (M.op (M.op x y) x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7114 eq7133
    | exact resolve eq7133 eq7114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7114 eq7133
  have eq7254 : (M.op x y) = (σ (M.op x y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7104 eq6687
    | exact resolve eq6687 eq7104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6687 eq7104
  have eq7281 : (σ x) = (M.op (σ x) (σ y)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq7254
    | exact resolve eq7254 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7254
  have eq7432 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7281 eq284
    | exact resolve eq284 eq7281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq284
  have eq7441 : (M.op (σ x) (σ y)) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq26 eq7432
    | exact resolve eq7432 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7432
  have eq7449 : (σ x) = (M.op (M.op x y) x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7281 eq7441
    | exact resolve eq7441 eq7281
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7441
  have eq7894 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq7141 eq392
    | exact resolve eq392 eq7141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq392
  have eq7949 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7141 eq6667
    | exact resolve eq6667 eq7141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7141
  have eq7986 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq7949
    | exact resolve eq7949 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7949
  have eq8152 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7986 eq27
    | exact resolve eq27 eq7986
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7986
  have eq11215 : (σ x) = (τ (σ x)) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq7449 eq6667
    | exact resolve eq6667 eq7449
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6667 eq7449
  have eq11261 : x = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq30 eq11215
    | exact resolve eq11215 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq11215
  have eq11324 : x = (σ x) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11261
       have r₂ := eq8152
       grind)
    | exact resolve eq11261 eq8152
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8152 eq11261
  have eq11387 : (M.op x y) = (M.op (σ x) y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11324
       grind)
    | exact superpose eq11324 eq18
    | exact resolve eq18 eq11324
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11466 : (M.op x y) ≠ (σ x) ∨ x = (M.op x y) := by grind
  clear eq11324
  have eq11606 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11387 eq7894
    | exact resolve eq7894 eq11387
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7894 eq11387
  have eq11631 : (M.op x y) = (σ x) ∨ (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq11606
  have eq11650 : (M.op x y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11631
       have r₂ := eq7129
       grind)
    | exact resolve eq11631 eq7129
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7129 eq11631
  have eq11664 : (M.op x y) ≠ (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11650 eq27
    | exact resolve eq27 eq11650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11678 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq11650 eq7281
    | exact resolve eq7281 eq11650
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7281 eq11650
  have eq11679 : (M.op x y) = (σ x) ∨ (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by grind
  clear eq11678
  have eq11682 : (M.op x y) = (σ (M.op x y)) ∨ x = (M.op x y) := by
    first
    | (have r₁ := eq11679
       have r₂ := eq11466
       grind)
    | exact resolve eq11679 eq11466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11466 eq11679
  have eq11688 : x = (M.op x y) := by
    first
    | (have r₁ := eq11682
       have r₂ := eq11664
       grind)
    | exact resolve eq11682 eq11664
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11664 eq11682
  have eq11692 : (M.op x y) = (M.op (M.op x y) y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq11688
       grind)
    | exact superpose eq11688 eq18
    | exact resolve eq18 eq11688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq11693 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq11688
       grind)
    | exact superpose eq11688 eq22
    | exact resolve eq22 eq11688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq11979 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq11693 eq20
    | exact resolve eq20 eq11693
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11693
  have eq12102 : (M.op x y) = (M.op (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq11692 eq181
    | exact resolve eq181 eq11692
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq11692
  have eq12140 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq12102
       have i₂ := eq885 sF0
       grind)
    | exact superpose eq885 eq12102
    | exact resolve eq12102 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12102
  have eq12160 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq12140 eq38
    | exact resolve eq38 eq12140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq12166 : (M.op (M.op x y) x) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq12140 eq1000
    | exact resolve eq1000 eq12140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1000
  have eq12177 : (M.op (M.op x y) x) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | (have i₁ := eq12166
       have i₂ := eq885 (σ sF0)
       grind)
    | exact superpose eq885 eq12166
    | exact resolve eq12166 eq885
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq885 eq12166
  have eq12181 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq12160
    | exact resolve eq12160 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12160
  have eq12183 : (σ (k (M.op x y) (M.op x y))) = (M.op (M.op x y) x) := by
    first
    | (have i₁ := eq12177
       have i₂ := eq10 sF0 sF0
       grind)
    | exact superpose eq10 eq12177
    | exact resolve eq12177 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12177
  have eq12186 : (σ x) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq11979 eq12181
    | exact resolve eq12181 eq11979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12181
  have eq12188 : (σ (k (M.op x y) (M.op x y))) = (M.op (M.op x y) (M.op x y)) := by
    first
    | (have i₁ := eq12183
       have i₂ := eq11688
       grind)
    | exact superpose eq11688 eq12183
    | exact resolve eq12183 eq11688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12183
  have eq12191 : (k (M.op x y) (M.op x y)) = (σ (k (M.op x y) (M.op x y))) := by
    first
    | exact superpose eq889 eq12188
    | exact resolve eq12188 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12188
  have eq12192 : (k (M.op x y) (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq42 eq12191
    | exact resolve eq12191 eq42
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq42 eq12191
  have eq12193 : (k (σ (M.op x y)) (σ x)) = (k (M.op x y) (M.op x y)) := by
    first
    | exact superpose eq11979 eq12192
    | exact resolve eq12192 eq11979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12192
  have eq12194 : (M.op x y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq12140 eq12193
    | exact resolve eq12193 eq12140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12193
  have eq12195 : (M.op x y) = (k (σ (M.op x y)) (σ x)) := by
    first
    | exact superpose eq20 eq12194
    | exact resolve eq12194 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12194
  have eq12196 : (M.op x y) = (k (σ x) (σ x)) := by
    first
    | exact superpose eq11979 eq12195
    | exact resolve eq12195 eq11979
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11979 eq12195
  have eq12247 : (M.op x y) = (σ x) := by
    first
    | exact superpose eq12196 eq12186
    | exact resolve eq12186 eq12196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12186
  have eq12249 : (k x x) = (τ (M.op x y)) := by
    first
    | exact superpose eq12196 eq98
    | exact resolve eq98 eq12196
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98 eq12196
  have eq12269 : (k (M.op x y) (M.op x y)) = (τ (M.op x y)) := by
    first
    | (have i₁ := eq12249
       have i₂ := eq11688
       grind)
    | exact superpose eq11688 eq12249
    | exact resolve eq12249 eq11688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12249
  have eq12274 : (M.op x y) = (τ (M.op x y)) := by
    first
    | exact superpose eq12140 eq12269
    | exact resolve eq12269 eq12140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12269
  have eq12284 : (M.op (σ x) (σ y)) = (M.op (M.op x y) (σ y)) := by
    first
    | exact superpose eq12247 eq26
    | exact resolve eq26 eq12247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26
  have eq12299 : ∀ X0 X1 : G, (M.op (M.op X0 X1) X0) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X1) := by
    intro X0 X1
    first
    | exact superpose eq12247 eq274
    | exact resolve eq274 eq12247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq274
  have eq12301 : (M.op (M.op x y) x) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq12247 eq287
    | exact resolve eq287 eq12247
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq287 eq12247
  have eq12335 : (M.op (M.op x y) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | (have i₁ := eq12301
       have i₂ := eq11688
       grind)
    | exact superpose eq11688 eq12301
    | exact resolve eq12301 eq11688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12301
  have eq12337 : ∀ X1 : G, (M.op (M.op x y) x) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X1) := by
    intro X1
    first
    | (have i₁ := eq12299 x X1
       have i₂ := eq413 x X1
       grind)
    | (have i₁ := eq12299 x y
       have i₂ := eq413 x X1
       grind)
    | exact superpose eq413 eq12299
    | exact resolve eq12299 eq413
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq413 eq12299
  have eq12353 : (k (M.op x y) (M.op x y)) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq889 eq12335
    | exact resolve eq12335 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12335
  have eq12355 : ∀ X1 : G, (M.op (M.op x y) (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X1) := by
    intro X1
    first
    | (have i₁ := eq12337 X1
       have i₂ := eq11688
       grind)
    | exact superpose eq11688 eq12337
    | exact resolve eq12337 eq11688
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11688 eq12337
  have eq12368 : (M.op x y) = (M.op (M.op (σ x) (σ y)) (M.op x y)) := by
    first
    | exact superpose eq12140 eq12353
    | exact resolve eq12353 eq12140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12353
  have eq12370 : ∀ X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op (M.op (σ x) (σ y)) (M.op x y)) X1) := by
    intro X1
    first
    | exact superpose eq889 eq12355
    | exact resolve eq12355 eq889
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq889 eq12355
  have eq12380 : ∀ X1 : G, (k (M.op x y) (M.op x y)) = (M.op (M.op x y) X1) := by
    intro X1
    first
    | exact superpose eq12368 eq12370
    | exact resolve eq12370 eq12368
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12368 eq12370
  have eq12388 : ∀ X1 : G, (M.op x y) = (M.op (M.op x y) X1) := by
    intro X1
    first
    | exact superpose eq12140 eq12380
    | exact resolve eq12380 eq12140
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12140 eq12380
  have eq12393 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq12274 eq14
    | exact resolve eq14 eq12274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12274
  have eq12409 : (M.op x y) = (σ (M.op x y)) := by
    first
    | exact superpose eq12393 eq20
    | exact resolve eq20 eq12393
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq12393
  have eq12953 : (M.op x y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq12388 eq12284
    | exact resolve eq12284 eq12388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12284 eq12388
  have eq13182 : (M.op x y) ≠ (σ (M.op x y)) := by
    first
    | exact superpose eq12953 eq27
    | exact resolve eq27 eq12953
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq12953
  have eq13208 : False := by grind
  exact eq13208
