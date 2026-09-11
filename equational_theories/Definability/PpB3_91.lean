import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = m(Y,Y) then m(Y,X) else if X = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_pyy_x_y_pyx_x_pyx_Equation838 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = M.op b b ∨ a ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = M.op b b ∨ a = b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = (M.op X1 X1) := by
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
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq65 (σ X0)
       grind)
    | exact superpose eq65 eq15
    | exact resolve eq15 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq68
    | exact resolve eq68 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq68
  have eq96 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op (σ X0) X1) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq492 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq509 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq492 X0 X1
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq492
    | (have j0 := eq492 X0 X1
       grind)
    | exact resolve eq492 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq492
  have eq625 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq509 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq509
    | exact resolve eq509 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq509
  have eq644 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ (M.op X1 X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq625 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq625
    | (have j0 := eq625 X0 X1
       grind)
    | exact resolve eq625 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq625
  have eq651 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (σ X1) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq644 X0 X1
       have j1 := eq96 X1 X0
       grind)
    | (have r₁ := eq644 X1 X0
       have r₂ := eq96 X0 X1
       grind)
    | (have r₁ := eq644 (M.op (σ X0) X1) (M.op X0 X0)
       have r₂ := eq96 X0 X1
       grind)
    | exact resolve eq644 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq644
  have eq657 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq651 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq651
    | exact resolve eq651 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq668 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq651 (σ X1) X0
       grind)
    | exact superpose eq651 eq15
    | (have j1 := eq651 (M.op (σ X0) (σ X1)) (k X1 X0)
       grind)
    | exact resolve eq15 eq651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq651
  have eq697 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq657 (τ X0) X1
       grind)
    | exact superpose eq657 eq19
    | (have j1 := eq657 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq657
  have eq786 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq697 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq697
    | exact resolve eq697 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq697
  have eq839 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq786 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq786
    | (have j0 := eq786 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq786 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq786
  have eq1003 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq668 x y
       grind)
    | exact superpose eq668 eq16
    | (have j1 := eq668 x y
       grind)
    | exact resolve eq16 eq668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq668
  have eq1024 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1003
       have i₂ := eq839 x y
       grind)
    | exact superpose eq839 eq1003
    | (have j1 := eq839 (σ x) (σ y)
       grind)
    | (have r₁ := eq1003
       have r₂ := eq839 x y
       grind)
    | (have r₁ := eq1003
       have r₂ := eq839 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1003
       have r₂ := eq839 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1003 eq839
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839 eq1003
  have eq1025 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1024
  have eq1028 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1025
       grind)
    | exact superpose eq1025 eq16
    | exact resolve eq16 eq1025
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1025
  have eq1029 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1028
       have r₂ := eq79 x
       grind)
    | exact resolve eq1028 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1028
  have eq1030 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1029
       grind)
    | exact superpose eq1029 eq16
    | exact resolve eq16 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1031 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1029
       grind)
    | exact superpose eq1029 eq10
    | exact resolve eq10 eq1029
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1029
  have eq1078 : x = y := by
    first
    | (have i₁ := eq1031
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1031
    | exact resolve eq1031 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1031
  have eq1079 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1030
       have i₂ := eq79 x
       grind)
    | exact superpose eq79 eq1030
    | exact resolve eq1030 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq1030
  have eq1080 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1079
       have i₂ := eq1078
       grind)
    | exact superpose eq1078 eq1079
    | exact resolve eq1079 eq1078
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1078 eq1079
  have eq1081 : False := by grind
  exact eq1081

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_x_y_pyx_pxx_pyx_Equation838 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ a = b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X0) = X0 := by
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
  have eq56 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq79 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
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
  have eq84 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op (τ X0) X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq85 : ∀ X0 : G, (M.op X0 X0) = (σ (k (τ X0) (τ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq56 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq56
    | exact resolve eq56 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq56
  have eq92 : ∀ X0 : G, (M.op X0 X0) = (k (σ (τ X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq85 X0
       have i₂ := eq19 X0 (τ X0)
       grind)
    | exact superpose eq19 eq85
    | (have j0 := eq85 X0
       grind)
    | exact resolve eq85 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq85
  have eq93 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq92 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq92
    | (have j0 := eq92 X0
       grind)
    | exact resolve eq92 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq92
  have eq94 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq93 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq93 X0
       have r₂ := eq12 X0 X0
       grind)
    | exact resolve eq93 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq93
  have eq97 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq94 (σ X0)
       grind)
    | exact superpose eq94 eq15
    | exact resolve eq15 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq108 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq97 X0
       have i₂ := eq94 X0
       grind)
    | exact superpose eq94 eq97
    | exact resolve eq97 eq94
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq94 eq97
  have eq178 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq79 x y
       grind)
    | exact superpose eq79 eq16
    | (have j1 := eq79 x y
       grind)
    | exact resolve eq16 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq184 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq79 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq765 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq84 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq84
    | exact resolve eq84 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq84
  have eq806 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq765 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq765
    | (have j0 := eq765 X0 X1
       grind)
    | exact resolve eq765 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq765
  have eq1116 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq178
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq178
    | (have j1 := eq14 (σ x) (σ y)
       grind)
    | (have r₁ := eq178
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq178
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq178 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq1117 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by grind
  clear eq1116
  have eq11120 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) := by
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
  have eq11121 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11120
       have r₂ := eq108 x
       grind)
    | exact resolve eq11120 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11120
  have eq11124 : y ≠ y ∨ y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq11121
       grind)
    | exact superpose eq11121 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq11121
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq11121
       grind)
    | exact resolve eq12 eq11121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11121
  have eq11159 : y = (k y x) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11124
  have eq11314 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq184 x y
       have i₂ := eq11159
       grind)
    | exact superpose eq11159 eq184
    | (have j0 := eq184 x y
       grind)
    | exact resolve eq184 eq11159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq184 eq11159
  have eq11331 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11314
  have eq11332 : (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq11331
  have eq11342 : y = (τ (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq11332
       grind)
    | exact superpose eq11332 eq10
    | exact resolve eq10 eq11332
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11332
  have eq11420 : x = y ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq11342
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq11342
    | exact resolve eq11342 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11342
  have eq11579 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11420
       grind)
    | exact superpose eq11420 eq16
    | exact resolve eq16 eq11420
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11420
  have eq11580 : (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq11579
       have r₂ := eq108 x
       grind)
    | exact resolve eq11579 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11579
  have eq11585 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11580
       grind)
    | exact superpose eq11580 eq16
    | exact resolve eq16 eq11580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq11600 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq11580
       grind)
    | exact superpose eq11580 eq12
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq11580
       grind)
    | exact resolve eq12 eq11580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11580
  have eq11639 : (σ y) = (k (σ y) (σ x)) := by grind
  clear eq11600
  have eq11646 : (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq11639
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq11639
    | exact resolve eq11639 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11639
  have eq11825 : (σ (M.op x y)) = (σ y) ∨ x = y ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq806 x y
       have i₂ := eq11646
       grind)
    | exact superpose eq11646 eq806
    | (have j0 := eq806 x y
       grind)
    | exact resolve eq806 eq11646
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq806 eq11646
  have eq11906 : x = y ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq11825
       have r₂ := eq11585
       grind)
    | exact resolve eq11825 eq11585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11825
  have eq12101 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq11906
       grind)
    | exact superpose eq11906 eq16
    | exact resolve eq16 eq11906
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11906
  have eq12109 : y = (M.op x y) := by
    first
    | (have r₁ := eq12101
       have r₂ := eq108 x
       grind)
    | exact resolve eq12101 eq108
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq108 eq12101
  have eq12280 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq11585
       have i₂ := eq12109
       grind)
    | exact superpose eq12109 eq11585
    | exact resolve eq11585 eq12109
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq11585 eq12109
  have eq12329 : False := by grind
  exact eq12329

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = X then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_x_x_y_pyx_pxx_pyx_Equation838 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 0) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = a ∨ a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X0 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X0 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X1 X1) = X0 := by
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
  have eq24 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k (τ X0) X1)
       have i₂ := eq19 X0 X1
       grind)
    | exact superpose eq19 eq10
    | exact resolve eq10 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30 : ∀ X0 X1 : G, (k X0 (τ X1)) = (τ (k (σ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 (τ X1))
       have i₂ := eq20 X1 X0
       grind)
    | exact superpose eq20 eq10
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20
  have eq66 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (σ X0) (M.op (σ X0) (σ X0)))) := by
    intro X0
    grind
  clear eq24
  have eq67 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq74 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k X0 (σ (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    grind
  clear eq19
  have eq75 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq74 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq74
    | (have j0 := eq74 X0
       grind)
    | exact resolve eq74 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq74
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq337 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq67
  have eq401 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq10 (M.op (τ X0) (τ X0))
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq10
    | (have j1 := eq75 X0
       grind)
    | exact resolve eq10 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75
  have eq480 : ∀ X0 : G, (τ X0) ≠ (τ (k X0 X0)) ∨ (τ X0) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have j0 := eq401 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq401
  have eq489 : ∀ X0 : G, (τ (σ X0)) ≠ (k X0 (τ (σ X0))) ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq480 (σ X0)
       have i₂ := eq30 X0 (σ X0)
       grind)
    | exact superpose eq30 eq480
    | (have j0 := eq480 (σ X0)
       grind)
    | exact resolve eq480 eq30
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq480
  have eq490 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (τ (σ X0)) = (M.op (τ (σ X0)) (τ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq489 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq489
    | (have j0 := eq489 X0
       grind)
    | exact resolve eq489 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq489
  have eq493 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq490 X0
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq490
    | (have j0 := eq490 X0
       grind)
    | exact resolve eq490 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq490
  have eq498 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq493 (σ X0)
       have i₂ := eq15 X0 X0
       grind)
    | exact superpose eq15 eq493
    | (have j0 := eq493 (σ X0)
       grind)
    | exact resolve eq493 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq851 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (σ X0) = (σ X1) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ X0 = X1 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq79 X1 X0
       have i₂ := eq14 X1 X0
       grind)
    | exact superpose eq14 eq79
    | (have j0 := eq79 X0 X1
       have j1 := eq14 (M.op (σ X0) (σ X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq79 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79
  have eq3162 : ∀ X0 : G, (k (σ (M.op X0 X0)) (σ X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  have eq3166 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq3162 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq3162
    | (have j0 := eq3162 X0
       grind)
    | exact resolve eq3162 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3162
  have eq3172 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    grind
  clear eq3166
  have eq12638 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq851 x y
       grind)
    | exact superpose eq851 eq16
    | (have j1 := eq851 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq851 x y
       grind)
    | (have r₁ := eq16
       have r₂ := eq851 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq16
       have r₂ := eq851 (M.op (σ x) (σ y)) (σ (M.op x y))
       grind)
    | exact resolve eq16 eq851
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq851
  have eq12670 : (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq12638
  have eq12688 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by grind
  clear eq12670
  have eq12730 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | (have i₁ := eq12688
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq12688
    | exact resolve eq12688 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12688
  have eq12741 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ y = (M.op x x) := by
    first
    | exact superpose eq14 eq12730
    | (have j1 := eq14 (σ (M.op x y)) (M.op (σ x) (σ y))
       grind)
    | exact resolve eq12730 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12730
  have eq12745 : y = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq12741
       have r₂ := eq16
       grind)
    | exact resolve eq12741 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12741
  have eq12754 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq3172 x
       have i₂ := eq12745
       grind)
    | exact superpose eq12745 eq3172
    | (have j0 := eq3172 x
       grind)
    | exact resolve eq3172 eq12745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3172
  have eq12775 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12754
  have eq12781 : (σ x) = (M.op (σ x) (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq12775
       have r₂ := eq16
       grind)
    | exact resolve eq12775 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12775
  have eq12862 : (τ (M.op (σ x) (σ x))) = (k (τ (σ x)) x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq66 x
       have i₂ := eq12781
       grind)
    | exact superpose eq12781 eq66
    | exact resolve eq66 eq12781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq12885 : (τ (M.op (σ x) (σ x))) = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12862
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12862
    | exact resolve eq12862 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12862
  have eq12887 : (k x x) = (τ (σ x)) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12781 eq12885
    | exact resolve eq12885 eq12781
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12781 eq12885
  have eq12888 : x = (k x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq12887
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12887
    | exact resolve eq12887 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12887
  have eq12897 : x ≠ x ∨ x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq493 x
       have i₂ := eq12888
       grind)
    | exact superpose eq12888 eq493
    | (have j0 := eq493 x
       grind)
    | (have r₁ := eq493 x
       have r₂ := eq12888
       grind)
    | exact resolve eq493 eq12888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq493 eq12888
  have eq12908 : x = (M.op x x) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq12897
  have eq12919 : x = y ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq12908 eq12745
    | exact resolve eq12745 eq12908
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12745 eq12908
  have eq12941 : (σ x) = (σ y) ∨ x = y := by grind
  clear eq12919
  have eq12944 : y = (τ (σ x)) ∨ x = y := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq12941
       grind)
    | exact superpose eq12941 eq10
    | exact resolve eq10 eq12941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12941
  have eq13120 : x = y ∨ x = y := by
    first
    | (have i₁ := eq12944
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq12944
    | exact resolve eq12944 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq12944
  have eq13121 : x = y := by grind
  clear eq13120
  have eq13122 : (M.op (σ x) (σ x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq13121
       grind)
    | exact superpose eq13121 eq16
    | exact resolve eq16 eq13121
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13121
  have eq13123 : (σ (M.op x x)) ≠ (σ (M.op x x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13122
       have i₂ := eq337 x
       grind)
    | exact superpose eq337 eq13122
    | (have j1 := eq337 x
       grind)
    | (have r₁ := eq13122
       have r₂ := eq337 x
       grind)
    | exact resolve eq13122 eq337
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq337
  have eq13124 : (σ x) = (M.op (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  clear eq13123
  have eq13126 : (σ x) ≠ (σ (M.op x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13122
       have i₂ := eq13124
       grind)
    | exact superpose eq13124 eq13122
    | exact resolve eq13122 eq13124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq13128 : (M.op (σ x) (σ x)) = (k (σ x) (σ x)) ∨ x = (M.op x x) := by grind
  have eq13150 : (M.op (σ x) (σ x)) = (σ (k x x)) ∨ x = (M.op x x) := by
    first
    | (have i₁ := eq13128
       have i₂ := eq15 x x
       grind)
    | exact superpose eq15 eq13128
    | exact resolve eq13128 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13128
  have eq13153 : (σ x) = (σ (k x x)) ∨ x = (M.op x x) := by
    first
    | exact superpose eq13124 eq13150
    | exact resolve eq13150 eq13124
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13124 eq13150
  have eq13155 : (σ x) = (σ (M.op x x)) ∨ x = (M.op x x) := by grind
  clear eq13153
  have eq13157 : x = (M.op x x) := by
    first
    | (have r₁ := eq13155
       have r₂ := eq13126
       grind)
    | exact resolve eq13155 eq13126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13126 eq13155
  have eq13159 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq13122
       have i₂ := eq13157
       grind)
    | exact superpose eq13157 eq13122
    | exact resolve eq13122 eq13157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13122
  have eq13160 : (M.op x x) = (k x x) := by grind
  have eq13181 : x = (k x x) := by
    first
    | (have i₁ := eq13160
       have i₂ := eq13157
       grind)
    | exact superpose eq13157 eq13160
    | exact resolve eq13160 eq13157
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq13157 eq13160
  have eq13191 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq498 x
       have i₂ := eq13181
       grind)
    | exact superpose eq13181 eq498
    | (have j0 := eq498 x
       grind)
    | exact resolve eq498 eq13181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq498 eq13181
  have eq13200 : (σ x) = (M.op (σ x) (σ x)) := by grind
  clear eq13191
  have eq13209 : False := by grind
  exact eq13209

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(Y,X) = m(Y,Y) then m(Y,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pyx_pyy_pyx_pyy_pyx_Equation838 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq22 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq13 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq22 X0
       have j1 := eq12 X0 X0
       grind)
    | (have r₁ := eq22 x
       have r₂ := eq12 X0 x
       grind)
    | exact resolve eq22 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22
  have eq27 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
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
  have eq31 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | (have i₁ := eq13 X1 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq13
    | (have j0 := eq13 X0 X0
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
  have eq37 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq14 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq38 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq31 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq39 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq27 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27
  have eq40 : ∀ X0 X1 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq39 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39
  have eq41 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq37 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq37 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq37 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37
  have eq47 : ∀ X0 X1 : G, (M.op X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq38 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq38 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq38 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq50 : ∀ X0 X1 : G, (M.op X0 X0) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq40 X0 X1
       have j1 := eq12 X1 X0
       grind)
    | (have r₁ := eq40 X1 X1
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq40 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq40
  have eq53 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq47 X0 X1
       have j1 := eq41 X0 X1
       grind)
    | (have r₁ := eq47 X0 X1
       have r₂ := eq41 X0 X1
       grind)
    | exact resolve eq47 eq41
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq47
  have eq55 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X0 X1) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X0 X1
       have i₂ := eq23 X0
       grind)
    | exact superpose eq23 eq53
    | (have j0 := eq53 X0 X1
       grind)
    | exact resolve eq53 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq53
  have eq103 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X1) ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq50 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq107 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq103 X0 X1
       have j1 := eq55 X1 X0
       grind)
    | (have r₁ := eq103 X1 X1
       have r₂ := eq55 X1 X1
       grind)
    | (have r₁ := eq103 X1 X0
       have r₂ := eq55 X0 X1
       grind)
    | exact resolve eq103 eq55
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq55 eq103
  have eq281 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq107 (σ X1) (σ X0)
       grind)
    | exact superpose eq107 eq15
    | exact resolve eq15 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq288 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq281 X0 X1
       have i₂ := eq107 X1 X0
       grind)
    | exact superpose eq107 eq281
    | exact resolve eq281 eq107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq281
  have eq291 : False := by grind
  exact eq291

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if X = Y then m(X,X) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_x_y_pyx_pxx_pyx_Equation838 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ X0 = X1 ∨ (M.op X1 X0) = (k X0 X1) := by
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
  have eq66 : ∀ X0 X1 : G, X0 ≠ X0 ∨ (k X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0 X1
    grind
  have eq68 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq66 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq66
  have eq77 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq68 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
  have eq78 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq77 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77
  have eq93 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq78 (σ X0)
       grind)
    | exact superpose eq78 eq15
    | exact resolve eq15 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq93 X0
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq93
    | exact resolve eq93 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq93
  have eq122 : ∀ X0 X1 : G, (σ X0) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (σ X0)
       have i₂ := eq104 X0
       grind)
    | exact superpose eq104 eq12
    | (have j0 := eq12 X1 (σ X0)
       grind)
    | exact resolve eq12 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (σ X0) = (σ (M.op X0 X0)) ∨ (σ X0) = X1 ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq104 X0
       have i₂ := eq14 X1 (σ X0)
       grind)
    | exact superpose eq14 eq104
    | (have j1 := eq14 (σ X0) (σ (M.op X0 X0))
       grind)
    | exact resolve eq104 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq148 : ∀ X0 X1 : G, (k X1 (σ X0)) = (M.op (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq141 X0 X1
       have j1 := eq122 X0 X1
       grind)
    | (have r₁ := eq141 X0 X1
       have r₂ := eq122 X0 X1
       grind)
    | (have r₁ := eq141 X0 (σ (M.op X0 X0))
       have r₂ := eq122 X0 X1
       grind)
    | (have r₁ := eq141 (M.op X0 X0) (σ X0)
       have r₂ := eq122 X0 X1
       grind)
    | exact resolve eq141 eq122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq122 eq141
  have eq170 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq148 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq148
    | exact resolve eq148 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq175 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq148 X0 (σ X1)
       grind)
    | exact superpose eq148 eq15
    | (have j1 := eq148 (k X1 X0) (M.op (σ X0) (σ X1))
       grind)
    | exact resolve eq15 eq148
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq148
  have eq182 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq170 (τ X0) X1
       grind)
    | exact superpose eq170 eq19
    | (have j1 := eq170 (k (σ X1) X0) (σ (M.op (τ X0) X1))
       grind)
    | exact resolve eq19 eq170
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq170
  have eq270 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq182 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq182
    | exact resolve eq182 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182
  have eq295 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq270 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq270
    | (have j0 := eq270 (σ (k X1 X0)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq270 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq270
  have eq1021 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq175 x y
       grind)
    | exact superpose eq175 eq16
    | (have j1 := eq175 x y
       grind)
    | exact resolve eq16 eq175
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175
  have eq1038 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq1021
       have i₂ := eq295 x y
       grind)
    | exact superpose eq295 eq1021
    | (have j1 := eq295 (σ x) (σ y)
       grind)
    | (have r₁ := eq1021
       have r₂ := eq295 x y
       grind)
    | (have r₁ := eq1021
       have r₂ := eq295 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq1021
       have r₂ := eq295 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq1021 eq295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq295 eq1021
  have eq1039 : x = y ∨ (σ x) = (σ y) := by grind
  clear eq1038
  have eq1041 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1039
       grind)
    | exact superpose eq1039 eq16
    | exact resolve eq16 eq1039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1039
  have eq1042 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq1041
       have r₂ := eq104 x
       grind)
    | exact resolve eq1041 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1041
  have eq1043 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1042
       grind)
    | exact superpose eq1042 eq16
    | exact resolve eq16 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1044 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq1042
       grind)
    | exact superpose eq1042 eq10
    | exact resolve eq10 eq1042
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1042
  have eq1088 : x = y := by
    first
    | (have i₁ := eq1044
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq1044
    | exact resolve eq1044 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1044
  have eq1089 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1043
       have i₂ := eq104 x
       grind)
    | exact superpose eq104 eq1043
    | exact resolve eq1043 eq104
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104 eq1043
  have eq1090 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq1089
       have i₂ := eq1088
       grind)
    | exact superpose eq1088 eq1089
    | exact resolve eq1089 eq1088
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1088 eq1089
  have eq1091 : False := by grind
  exact eq1091

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_x_pyx_Equation838 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a a ≠ M.op b a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a a = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = (M.op X0 X0) ∨ X0 = X1 := by
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
  have eq61 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (σ X0) = (k (σ X0) X1) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (σ X0) X1
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 (σ X0) X1
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq95 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X0 X1
       have i₂ := eq14 X1 (τ X0)
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 X1 (τ X0)
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq96 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq101 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq96
    | (have j0 := eq96 X0 X1
       grind)
    | exact resolve eq96 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq137 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq101 x y
       grind)
    | exact superpose eq101 eq16
    | (have j1 := eq101 x y
       grind)
    | exact resolve eq16 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op (M.op X2 (σ X0)) (σ (k X0 X1)))) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) X2 (σ X1)
       have i₂ := eq101 X1 X0
       grind)
    | exact superpose eq101 eq9
    | (have j1 := eq101 X1 X0
       grind)
    | exact resolve eq9 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 X2 : G, (σ X0) = (M.op (σ X0) (M.op (σ (k X0 X1)) (M.op X2 (σ X0)))) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X0) (σ X1) X2
       have i₂ := eq101 X1 X0
       grind)
    | exact superpose eq101 eq9
    | (have j1 := eq101 X1 X0
       grind)
    | exact resolve eq9 eq101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101
  have eq998 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq95 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq95
    | exact resolve eq95 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq1049 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X1 X1) = (M.op X0 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq998 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq998
    | (have j0 := eq998 X0 X1
       grind)
    | exact resolve eq998 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq1497 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq137
       have i₂ := eq1049 x y
       grind)
    | exact superpose eq1049 eq137
    | (have j1 := eq1049 x y
       grind)
    | (have r₁ := eq137
       have r₂ := eq1049 x y
       grind)
    | (have r₁ := eq137
       have r₂ := eq1049 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq137
       have r₂ := eq1049 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq137 eq1049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq1498 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq1497
  have eq21847 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1498
       grind)
    | exact superpose eq1498 eq16
    | exact resolve eq16 eq1498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498
  have eq21848 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq21847
       have r₂ := eq22 x
       grind)
    | exact resolve eq21847 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21847
  have eq21850 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21848
       grind)
    | exact superpose eq21848 eq16
    | exact resolve eq16 eq21848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21856 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq61 y (σ x)
       have i₂ := eq21848
       grind)
    | exact superpose eq21848 eq61
    | (have j0 := eq61 y (σ x)
       grind)
    | (have r₁ := eq61 y (σ x)
       have r₂ := eq21848
       grind)
    | exact resolve eq61 eq21848
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq21848
  have eq21915 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq21856
  have eq21916 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq21915
  have eq21941 : (σ x) = (σ y) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq21916
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq21916
    | exact resolve eq21916 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21916
  have eq22240 : y = (τ (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq21941
       grind)
    | exact superpose eq21941 eq10
    | exact resolve eq10 eq21941
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21941
  have eq22388 : x = y ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq22240
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22240
    | exact resolve eq22240 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22240
  have eq22390 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k y x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22388
       grind)
    | exact superpose eq22388 eq16
    | exact resolve eq16 eq22388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22388
  have eq22391 : (M.op x y) = (M.op y y) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq22390
       have r₂ := eq22 x
       grind)
    | exact resolve eq22390 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22390
  have eq22682 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = (k y X0) ∨ y = X0 ∨ (σ y) = (σ (k y x)) := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq22391
       grind)
    | exact superpose eq22391 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq22391
       grind)
    | exact resolve eq13 eq22391
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22391
  have eq23419 : x = y ∨ y = (k y x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have j0 := eq22682 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22682
  have eq23420 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23419
       grind)
    | exact superpose eq23419 eq16
    | exact resolve eq16 eq23419
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23419
  have eq23424 : y = (k y x) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq23420
       have r₂ := eq22 x
       grind)
    | exact resolve eq23420 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23420
  have eq23704 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23424
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq23424
    | (have j1 := eq14 y x
       grind)
    | exact resolve eq23424 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23424
  have eq25368 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23704
       grind)
    | exact superpose eq23704 eq16
    | exact resolve eq16 eq23704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23704
  have eq25386 : y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq25368
       have r₂ := eq22 x
       grind)
    | exact resolve eq25368 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25368
  have eq25540 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 y))) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq25386
       grind)
    | exact superpose eq25386 eq9
    | exact resolve eq9 eq25386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25541 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 x
       have i₂ := eq25386
       grind)
    | exact superpose eq25386 eq9
    | exact resolve eq9 eq25386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27000 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq25540 (M.op x y)
       have i₂ := eq25541 x
       grind)
    | exact superpose eq25541 eq25540
    | exact resolve eq25540 eq25541
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25540 eq25541
  have eq27051 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by grind
  clear eq27000
  have eq27057 : (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq27051
       grind)
    | exact superpose eq27051 eq10
    | exact resolve eq10 eq27051
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27051
  have eq27214 : y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq27057
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq27057
    | exact resolve eq27057 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27057
  have eq27712 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 y))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq27214
       grind)
    | exact superpose eq27214 eq9
    | exact resolve eq9 eq27214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27761 : y = (M.op y (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq27712 x
       have i₂ := eq27214
       grind)
    | exact superpose eq27214 eq27712
    | exact resolve eq27712 eq27214
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27214
  have eq27816 : y = (M.op y (M.op y y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq27761
  have eq28300 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq27712 y
       have i₂ := eq27816
       grind)
    | exact superpose eq27816 eq27712
    | exact resolve eq27712 eq27816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27712 eq27816
  have eq28355 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq28300
  have eq28358 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq21850
       have i₂ := eq28355
       grind)
    | exact superpose eq28355 eq21850
    | exact resolve eq21850 eq28355
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21850
  have eq28459 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq28355
  have eq28461 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq28358
       have r₂ := eq25386
       grind)
    | exact resolve eq28358 eq25386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25386 eq28358
  have eq28462 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq28461
       have r₂ := eq28459
       grind)
    | exact resolve eq28461 eq28459
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28459 eq28461
  have eq28949 : y = (τ (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq28462
       grind)
    | exact superpose eq28462 eq10
    | exact resolve eq10 eq28462
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28462
  have eq29107 : x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq28949
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq28949
    | exact resolve eq28949 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28949
  have eq29514 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29107
       grind)
    | exact superpose eq29107 eq16
    | exact resolve eq16 eq29107
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29107
  have eq29532 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq29514
       have r₂ := eq22 x
       grind)
    | exact resolve eq29514 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29514
  have eq29539 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = (k y X0) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq13 y X0
       have i₂ := eq29532
       grind)
    | exact superpose eq29532 eq13
    | (have j0 := eq13 y X0
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq29532
       grind)
    | exact resolve eq13 eq29532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30783 : y = (k y x) ∨ x = y := by
    first
    | (have j0 := eq29539 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29539
  have eq30787 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq137
       have i₂ := eq30783
       grind)
    | exact superpose eq30783 eq137
    | exact resolve eq137 eq30783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq30789 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (σ y)) (σ y))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq139 y x X0
       have i₂ := eq30783
       grind)
    | exact superpose eq30783 eq139
    | (have j0 := eq139 y x x
       grind)
    | exact resolve eq139 eq30783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq30790 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (σ y)))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq140 y x X0
       have i₂ := eq30783
       grind)
    | exact superpose eq30783 eq140
    | (have j0 := eq140 y x x
       grind)
    | exact resolve eq140 eq30783
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq30783
  have eq30847 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq30790 X0
       have i₂ := eq29532
       grind)
    | exact superpose eq29532 eq30790
    | (have j0 := eq30790 X0
       grind)
    | exact resolve eq30790 eq29532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30790
  have eq30848 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (M.op X0 (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq30789 X0
       have i₂ := eq29532
       grind)
    | exact superpose eq29532 eq30789
    | (have j0 := eq30789 X0
       grind)
    | exact resolve eq30789 eq29532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30789
  have eq30849 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq30787
       have i₂ := eq29532
       grind)
    | exact superpose eq29532 eq30787
    | exact resolve eq30787 eq29532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30787
  have eq30858 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq30847 X0
       grind)
    | (have r₁ := eq30847 X0
       have r₂ := eq16
       grind)
    | exact resolve eq30847 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30847
  have eq30859 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq30848 X0
       grind)
    | (have r₁ := eq30848 X0
       have r₂ := eq16
       grind)
    | exact resolve eq30848 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30848
  have eq30860 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq30849
       have r₂ := eq16
       grind)
    | exact resolve eq30849 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30849
  have eq47693 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq30858 (M.op x (σ y))
       have i₂ := eq30859 x
       grind)
    | exact superpose eq30859 eq30858
    | exact resolve eq30858 eq30859
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30858 eq30859
  have eq47748 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq47693
  have eq47755 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq47748
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq47748
    | exact resolve eq47748 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47748
  have eq47760 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq47755
       have i₂ := eq29532
       grind)
    | exact superpose eq29532 eq47755
    | exact resolve eq47755 eq29532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29532 eq47755
  have eq47761 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq47760
       have r₂ := eq30860
       grind)
    | exact resolve eq47760 eq30860
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30860 eq47760
  have eq47762 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq47761
       grind)
    | exact superpose eq47761 eq16
    | exact resolve eq16 eq47761
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47761
  have eq47810 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq47762
       have r₂ := eq22 x
       grind)
    | exact resolve eq47762 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47762
  have eq48208 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq47810
       grind)
    | exact superpose eq47810 eq16
    | exact resolve eq16 eq47810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48228 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq47810
       grind)
    | exact superpose eq47810 eq10
    | exact resolve eq10 eq47810
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47810
  have eq48434 : x = y := by
    first
    | (have i₁ := eq48228
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq48228
    | exact resolve eq48228 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48228
  have eq48437 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq48208
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq48208
    | exact resolve eq48208 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq48208
  have eq48445 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq48437
       have i₂ := eq48434
       grind)
    | exact superpose eq48434 eq48437
    | exact resolve eq48437 eq48434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48434 eq48437
  have eq48446 : False := by grind
  exact eq48446

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,Y) = m(Y,Y) then Y else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxy_pyy_pxx_y_pxy_Equation838 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) Law838 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op a b ≠ M.op b b ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op a b = M.op b b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 (M.op (M.op X1 X0) (M.op X2 X0))) = X0 := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X0) ∨ X0 ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (k X0 X1) = X1 ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
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
  have eq21 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    grind
  have eq22 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    grind
  clear eq21
  have eq61 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (σ X0) = (k X1 (σ X0)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X1 (σ X0)
       have i₂ := eq22 X0
       grind)
    | exact superpose eq22 eq13
    | (have j0 := eq13 X1 (σ X0)
       grind)
    | exact resolve eq13 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (M.op (σ X1) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq98 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op (τ X0) X1)) ∨ (M.op X1 X1) = (M.op (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq14 (τ X0) X1
       grind)
    | exact superpose eq14 eq18
    | (have j1 := eq14 (τ X0) X1
       grind)
    | exact resolve eq18 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq99 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq96 X0 X1
       have i₂ := eq22 X1
       grind)
    | exact superpose eq22 eq96
    | (have j0 := eq96 X0 X1
       grind)
    | exact resolve eq96 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq137 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq99 x y
       grind)
    | exact superpose eq99 eq16
    | (have j1 := eq99 x y
       grind)
    | exact resolve eq16 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq139 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (M.op (M.op X2 (σ X1)) (σ (k X0 X1)))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) X2 (σ X0)
       have i₂ := eq99 X0 X1
       grind)
    | exact superpose eq99 eq9
    | (have j1 := eq99 X0 X1
       grind)
    | exact resolve eq9 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq140 : ∀ X0 X1 X2 : G, (σ X1) = (M.op (σ X1) (M.op (σ (k X0 X1)) (M.op X2 (σ X1)))) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq9 (σ X1) (σ X0) X2
       have i₂ := eq99 X0 X1
       grind)
    | exact superpose eq99 eq9
    | (have j1 := eq99 X0 X1
       grind)
    | exact resolve eq9 eq99
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq998 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq98 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq98
    | exact resolve eq98 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq1049 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X1) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq998 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq998
    | (have j0 := eq998 X0 X1
       grind)
    | exact resolve eq998 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq998
  have eq1497 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq137
       have i₂ := eq1049 x y
       grind)
    | exact superpose eq1049 eq137
    | (have j1 := eq1049 x y
       grind)
    | (have r₁ := eq137
       have r₂ := eq1049 x y
       grind)
    | (have r₁ := eq137
       have r₂ := eq1049 (σ (M.op x y)) (σ (k x y))
       grind)
    | (have r₁ := eq137
       have r₂ := eq1049 (σ (k x y)) (σ (M.op x y))
       grind)
    | exact resolve eq137 eq1049
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1049
  have eq1498 : x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by grind
  clear eq1497
  have eq21832 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq1498
       grind)
    | exact superpose eq1498 eq16
    | exact resolve eq16 eq1498
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1498
  have eq21833 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq21832
       have r₂ := eq22 x
       grind)
    | exact resolve eq21832 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21832
  have eq21835 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq21833
       grind)
    | exact superpose eq21833 eq16
    | exact resolve eq16 eq21833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq21841 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq61 y (σ x)
       have i₂ := eq21833
       grind)
    | exact superpose eq21833 eq61
    | (have j0 := eq61 y (σ x)
       grind)
    | (have r₁ := eq61 y (σ x)
       have r₂ := eq21833
       grind)
    | exact resolve eq61 eq21833
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq21833
  have eq21900 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq21841
  have eq21901 : (σ y) = (k (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq21900
  have eq21926 : (σ x) = (σ y) ∨ (σ y) = (σ (k x y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq21901
       have i₂ := eq15 x y
       grind)
    | exact superpose eq15 eq21901
    | exact resolve eq21901 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21901
  have eq22216 : y = (τ (σ x)) ∨ (σ y) = (σ (k x y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq21926
       grind)
    | exact superpose eq21926 eq10
    | exact resolve eq10 eq21926
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21926
  have eq22364 : x = y ∨ (σ y) = (σ (k x y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq22216
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq22216
    | exact resolve eq22216 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22216
  have eq22366 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ y) = (σ (k x y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq22364
       grind)
    | exact superpose eq22364 eq16
    | exact resolve eq16 eq22364
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22364
  have eq22367 : (M.op x y) = (M.op y y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq22366
       have r₂ := eq22 x
       grind)
    | exact resolve eq22366 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22366
  have eq22657 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = (k X0 y) ∨ y = X0 ∨ (σ y) = (σ (k x y)) := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq22367
       grind)
    | exact superpose eq22367 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq22367
       grind)
    | exact resolve eq13 eq22367
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22367
  have eq23351 : x = y ∨ y = (k x y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have j0 := eq22657 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22657
  have eq23352 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k x y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23351
       grind)
    | exact superpose eq23351 eq16
    | exact resolve eq16 eq23351
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23351
  have eq23356 : y = (k x y) ∨ (σ y) = (σ (k x y)) := by
    first
    | (have r₁ := eq23352
       have r₂ := eq22 x
       grind)
    | exact resolve eq23352 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23352
  have eq23679 : x = y ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq23356
       have i₂ := eq14 x y
       grind)
    | exact superpose eq14 eq23356
    | (have j1 := eq14 x y
       grind)
    | exact resolve eq23356 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23356
  have eq25343 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq23679
       grind)
    | exact superpose eq23679 eq16
    | exact resolve eq16 eq23679
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23679
  have eq25361 : y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq25343
       have r₂ := eq22 x
       grind)
    | exact resolve eq25343 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25343
  have eq25515 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 y))) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq25361
       grind)
    | exact superpose eq25361 eq9
    | exact resolve eq9 eq25361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq25516 : ∀ X0 : G, y = (M.op y (M.op (M.op X0 y) y)) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq9 y X0 x
       have i₂ := eq25361
       grind)
    | exact superpose eq25361 eq9
    | exact resolve eq9 eq25361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq26975 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have i₁ := eq25515 (M.op x y)
       have i₂ := eq25516 x
       grind)
    | exact superpose eq25516 eq25515
    | exact resolve eq25515 eq25516
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25515 eq25516
  have eq27026 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by grind
  clear eq26975
  have eq27032 : (M.op x y) = (τ (σ y)) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op x y)
       have i₂ := eq27026
       grind)
    | exact superpose eq27026 eq10
    | exact resolve eq10 eq27026
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27026
  have eq27189 : y = (M.op x y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq27032
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq27032
    | exact resolve eq27032 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27032
  have eq27687 : ∀ X0 : G, y = (M.op y (M.op y (M.op X0 y))) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    intro X0
    first
    | (have i₁ := eq9 y x X0
       have i₂ := eq27189
       grind)
    | exact superpose eq27189 eq9
    | exact resolve eq9 eq27189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq27736 : y = (M.op y (M.op y y)) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) := by
    first
    | (have i₁ := eq27687 x
       have i₂ := eq27189
       grind)
    | exact superpose eq27189 eq27687
    | exact resolve eq27687 eq27189
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27189
  have eq27791 : y = (M.op y (M.op y y)) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq27736
  have eq28275 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ y = (M.op y y) ∨ y = (M.op y y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq27687 y
       have i₂ := eq27791
       grind)
    | exact superpose eq27791 eq27687
    | exact resolve eq27687 eq27791
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27687 eq27791
  have eq28330 : y = (M.op y y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq28275
  have eq28333 : (σ (M.op x y)) ≠ (σ y) ∨ y = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq21835
       have i₂ := eq28330
       grind)
    | exact superpose eq28330 eq21835
    | exact resolve eq21835 eq28330
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21835
  have eq28434 : y ≠ (M.op x y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq28330
  have eq28436 : y = (M.op x y) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq28333
       have r₂ := eq25361
       grind)
    | exact resolve eq28333 eq25361
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25361 eq28333
  have eq28437 : (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq28436
       have r₂ := eq28434
       grind)
    | exact resolve eq28436 eq28434
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28434 eq28436
  have eq28956 : y = (τ (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq28437
       grind)
    | exact superpose eq28437 eq10
    | exact resolve eq10 eq28437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28437
  have eq29114 : x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq28956
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq28956
    | exact resolve eq28956 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28956
  have eq29514 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq29114
       grind)
    | exact superpose eq29114 eq16
    | exact resolve eq16 eq29114
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29114
  have eq29532 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq29514
       have r₂ := eq22 x
       grind)
    | exact resolve eq29514 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29514
  have eq29539 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = (k X0 y) ∨ y = X0 := by
    intro X0
    first
    | (have i₁ := eq13 X0 y
       have i₂ := eq29532
       grind)
    | exact superpose eq29532 eq13
    | (have j0 := eq13 X0 y
       grind)
    | (have r₁ := eq13 x y
       have r₂ := eq29532
       grind)
    | exact resolve eq13 eq29532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq30725 : y = (k x y) ∨ x = y := by
    first
    | (have j0 := eq29539 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29539
  have eq30729 : (σ (M.op x y)) ≠ (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq137
       have i₂ := eq30725
       grind)
    | exact superpose eq30725 eq137
    | exact resolve eq137 eq30725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq137
  have eq30731 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (σ y)) (σ y))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq139 x y X0
       have i₂ := eq30725
       grind)
    | exact superpose eq30725 eq139
    | (have j0 := eq139 x y x
       grind)
    | exact resolve eq139 eq30725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq139
  have eq30732 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (σ y)))) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq140 x y X0
       have i₂ := eq30725
       grind)
    | exact superpose eq30725 eq140
    | (have j0 := eq140 x y x
       grind)
    | exact resolve eq140 eq30725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq140 eq30725
  have eq30789 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq30732 X0
       have i₂ := eq29532
       grind)
    | exact superpose eq29532 eq30732
    | (have j0 := eq30732 X0
       grind)
    | exact resolve eq30732 eq29532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30732
  have eq30790 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ y) (M.op (M.op X0 (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq30731 X0
       have i₂ := eq29532
       grind)
    | exact superpose eq29532 eq30731
    | (have j0 := eq30731 X0
       grind)
    | exact resolve eq30731 eq29532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30731
  have eq30791 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq30729
       have i₂ := eq29532
       grind)
    | exact superpose eq29532 eq30729
    | exact resolve eq30729 eq29532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30729
  have eq30800 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (σ y) (M.op X0 (σ y)))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq30789 X0
       grind)
    | (have r₁ := eq30789 X0
       have r₂ := eq16
       grind)
    | exact resolve eq30789 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30789
  have eq30801 : ∀ X0 : G, (σ y) = (M.op (σ y) (M.op (M.op X0 (σ y)) (σ y))) ∨ (σ x) = (σ y) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq30790 X0
       grind)
    | (have r₁ := eq30790 X0
       have r₂ := eq16
       grind)
    | exact resolve eq30790 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30790
  have eq30802 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq30791
       have r₂ := eq16
       grind)
    | exact resolve eq30791 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30791
  have eq47636 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq30800 (M.op x (σ y))
       have i₂ := eq30801 x
       grind)
    | exact superpose eq30801 eq30800
    | exact resolve eq30800 eq30801
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30800 eq30801
  have eq47691 : (σ y) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by grind
  clear eq47636
  have eq47698 : (σ y) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq47691
       have i₂ := eq22 y
       grind)
    | exact superpose eq22 eq47691
    | exact resolve eq47691 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47691
  have eq47703 : (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq47698
       have i₂ := eq29532
       grind)
    | exact superpose eq29532 eq47698
    | exact resolve eq47698 eq29532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29532 eq47698
  have eq47704 : x = y ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq47703
       have r₂ := eq30802
       grind)
    | exact resolve eq47703 eq30802
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30802 eq47703
  have eq47705 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq47704
       grind)
    | exact superpose eq47704 eq16
    | exact resolve eq16 eq47704
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47704
  have eq47753 : (σ x) = (σ y) := by
    first
    | (have r₁ := eq47705
       have r₂ := eq22 x
       grind)
    | exact resolve eq47705 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47705
  have eq48169 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq47753
       grind)
    | exact superpose eq47753 eq16
    | exact resolve eq16 eq47753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq48189 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq47753
       grind)
    | exact superpose eq47753 eq10
    | exact resolve eq10 eq47753
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47753
  have eq48395 : x = y := by
    first
    | (have i₁ := eq48189
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq48189
    | exact resolve eq48189 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48189
  have eq48398 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq48169
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq48169
    | exact resolve eq48169 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq48169
  have eq48406 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq48398
       have i₂ := eq48395
       grind)
    | exact superpose eq48395 eq48398
    | exact resolve eq48398 eq48395
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq48395 eq48398
  have eq48407 : False := by grind
  exact eq48407

/-- `Equation838`: `x = x ◇ ((y ◇ x) ◇ (z ◇ x))`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pyx_x_pxx_x_pyx_Equation838 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law838 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law838.models_iff G M).mp hM
  have ht : ∀ a b : G, a ≠ b ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, a = b ∨ M.op b a ≠ a ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, a = b ∨ M.op b a = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b a) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ X0 = X1 := by
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
  clear eq19
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
  have eq117 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
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
  have eq119 : ∀ X0 X1 : G, (τ X1) = (M.op X0 (τ X1)) ∨ (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (τ X1) = X0 := by
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
  have eq663 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq117 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq117
  have eq4091 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (τ X0) = (k (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq13 (τ X0) X1
       have i₂ := eq119 X1 X0
       grind)
    | exact superpose eq119 eq13
    | (have j0 := eq13 (τ X0) X1
       have j1 := eq119 X1 X0
       grind)
    | (have r₁ := eq13 (τ X1) X0
       have r₂ := eq119 X0 X1
       grind)
    | (have r₁ := eq13 (τ X1) X1
       have r₂ := eq119 (M.op X1 (τ X1)) X1
       grind)
    | exact resolve eq13 eq119
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq119
  have eq4104 : ∀ X0 X1 : G, (τ X0) ≠ (τ X0) ∨ (τ X0) = X1 ∨ (τ X0) = (k (τ X0) X1) ∨ (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) := by
    intro X0 X1
    first
    | (have j0 := eq4091 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4091
  have eq4105 : ∀ X0 X1 : G, (k X0 (σ X1)) = (σ (M.op X1 (τ X0))) ∨ (τ X0) = (k (τ X0) X1) ∨ (τ X0) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq4104 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4104
  have eq4394 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4105 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4105
    | exact resolve eq4105 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4105
  have eq4461 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (k X0 X1) = X0 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4394 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq4394
    | (have j0 := eq4394 X0 X1
       grind)
    | exact resolve eq4394 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4394
  have eq4510 : ∀ X0 X1 : G, (k X1 X0) = (τ (σ (M.op X0 X1))) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X1 X0)
       have i₂ := eq4461 X1 X0
       grind)
    | exact superpose eq4461 eq10
    | (have j1 := eq4461 X1 X0
       grind)
    | exact resolve eq10 eq4461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq4562 : ∀ X0 X1 : G, (k X1 X0) = (M.op X0 X1) ∨ (k X1 X0) = X1 ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq4510 X0 X1
       have i₂ := eq10 (M.op X0 X1)
       grind)
    | exact superpose eq10 eq4510
    | (have j0 := eq4510 X0 X1
       grind)
    | exact resolve eq4510 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4510
  have eq4591 : ∀ X0 X1 : G, (k X1 (σ X0)) = X1 ∨ (k (τ X1) X0) = (τ (M.op (σ X0) X1)) ∨ (σ X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq28 X1 X0
       have i₂ := eq4562 (σ X0) X1
       grind)
    | exact superpose eq4562 eq28
    | (have j1 := eq4562 (σ X0) X1
       grind)
    | exact resolve eq28 eq4562
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq4562
  have eq4907 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 (τ (σ X1))) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq37 X0 (σ X1)
       have i₂ := eq4591 X1 (σ X0)
       grind)
    | exact superpose eq4591 eq37
    | (have j1 := eq4591 X1 (σ X0)
       grind)
    | exact resolve eq37 eq4591
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq4591
  have eq4973 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4907 X0 X1
       have i₂ := eq10 X1
       grind)
    | exact superpose eq10 eq4907
    | (have j0 := eq4907 X0 X1
       grind)
    | exact resolve eq4907 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4907
  have eq5006 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k (τ (σ X0)) X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq4973 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq4973
    | (have j0 := eq4973 X0 X1
       grind)
    | exact resolve eq4973 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4973
  have eq5016 : ∀ X0 X1 : G, (k X0 X1) = X0 ∨ (k X0 X1) = (τ (M.op (σ X1) (σ X0))) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5006 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq5006
    | (have j0 := eq5006 X0 X1
       grind)
    | exact resolve eq5006 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5006
  have eq5183 : ∀ X0 X1 : G, (τ X0) = (τ (k X0 X1)) ∨ (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) (σ (τ X0)))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5016 (τ X1) (τ X0)
       have i₂ := eq45 X0 X1
       grind)
    | exact superpose eq45 eq5016
    | (have j0 := eq5016 (τ X0) (τ X1)
       grind)
    | exact resolve eq5016 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq5016
  have eq5384 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op (σ (τ X1)) X0)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5183 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5183
    | (have j0 := eq5183 X0 X1
       grind)
    | exact resolve eq5183 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5183
  have eq5460 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (τ X0) = (τ (k X0 X1)) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5384 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5384
    | (have j0 := eq5384 X0 X1
       grind)
    | exact resolve eq5384 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5384
  have eq5520 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5460 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq5460
    | (have j0 := eq5460 X0 X1
       grind)
    | exact resolve eq5460 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5460
  have eq5578 : ∀ X0 X1 : G, (τ (k X0 X1)) = (τ (M.op X1 X0)) ∨ X0 = X1 ∨ (τ X0) = (τ (k X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq5520 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5520
    | (have j0 := eq5520 X0 X1
       grind)
    | exact resolve eq5520 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5520
  have eq5667 : ∀ X0 X1 : G, (k X1 X0) = (σ (τ (M.op X0 X1))) ∨ X0 = X1 ∨ (τ X1) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq11 (k X1 X0)
       have i₂ := eq5578 X1 X0
       grind)
    | exact superpose eq5578 eq11
    | (have j1 := eq5578 (k X1 X0) (σ (τ (M.op X0 X1)))
       grind)
    | exact resolve eq11 eq5578
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5578
  have eq5793 : ∀ X0 X1 : G, (τ X1) = (τ (k X1 X0)) ∨ X0 = X1 ∨ (k X1 X0) = (M.op X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq5667 X0 X1
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq5667
    | (have j0 := eq5667 X0 X1
       grind)
    | exact resolve eq5667 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5667
  have eq5887 : ∀ X0 X1 : G, (τ (σ X0)) = (τ (σ (k X0 X1))) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5793 (σ X1) (σ X0)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq5793
    | (have j0 := eq5793 (τ (σ X0)) (τ (σ (k X0 X1)))
       grind)
    | exact resolve eq5793 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5793
  have eq6061 : ∀ X0 X1 : G, (τ (σ X0)) = (k X0 X1) ∨ (σ X0) = (σ X1) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq5887 X0 X1
       have i₂ := eq10 (k X0 X1)
       grind)
    | exact superpose eq10 eq5887
    | (have j0 := eq5887 X0 X1
       grind)
    | exact resolve eq5887 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5887
  have eq6066 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) ∨ (k X0 X1) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq6061 X0 X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq6061
    | (have j0 := eq6061 X0 X1
       grind)
    | exact resolve eq6061 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6061
  have eq6592 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ x) = (σ y) ∨ y = (k y x) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6066 y x
       grind)
    | exact superpose eq6066 eq16
    | (have j1 := eq6066 x y
       grind)
    | exact resolve eq16 eq6066
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6066
  have eq6646 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ y = (M.op x y) ∨ x = y := by
    first
    | (have i₁ := eq6592
       have i₂ := eq14 y x
       grind)
    | exact superpose eq14 eq6592
    | (have j1 := eq14 y x
       grind)
    | (have r₁ := eq6592
       have r₂ := eq14 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq6592
       have r₂ := eq14 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq6592 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6647 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ y = (k y x) ∨ x = y := by
    first
    | (have i₁ := eq6592
       have i₂ := eq4461 y x
       grind)
    | exact superpose eq4461 eq6592
    | (have j1 := eq4461 y x
       grind)
    | (have r₁ := eq6592
       have r₂ := eq4461 y x
       grind)
    | (have r₁ := eq6592
       have r₂ := eq4461 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq6592
       have r₂ := eq4461 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq6592 eq4461
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4461 eq6592
  have eq6650 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (k y x) ∨ x = y := by grind
  clear eq6647
  have eq6651 : x = y ∨ y = (k y x) ∨ (σ x) = (σ y) := by grind
  clear eq6650
  have eq6652 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) ∨ y = (M.op x y) ∨ x = y := by grind
  clear eq6646
  have eq6653 : x = y ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by grind
  clear eq6652
  have eq6656 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6651
       grind)
    | exact superpose eq6651 eq16
    | exact resolve eq16 eq6651
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6651
  have eq6657 : y = (k y x) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6656
       have r₂ := eq22 x
       grind)
    | exact resolve eq6656 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6656
  have eq6661 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq663 x y
       have i₂ := eq6657
       grind)
    | exact superpose eq6657 eq663
    | (have j0 := eq663 x y
       grind)
    | exact resolve eq663 eq6657
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq663 eq6657
  have eq6668 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq6661
  have eq6669 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) := by grind
  clear eq6668
  have eq6673 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6653
       grind)
    | exact superpose eq6653 eq16
    | exact resolve eq16 eq6653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6653
  have eq6674 : y = (M.op x y) ∨ (σ x) = (σ y) := by
    first
    | (have r₁ := eq6673
       have r₂ := eq22 x
       grind)
    | exact resolve eq6673 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6673
  have eq6691 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6669
       grind)
    | exact superpose eq6669 eq16
    | exact resolve eq16 eq6669
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6669
  have eq6723 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq6691
       have i₂ := eq6674
       grind)
    | exact superpose eq6674 eq6691
    | exact resolve eq6691 eq6674
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6674 eq6691
  have eq6724 : (σ y) ≠ (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq6723
  have eq6725 : (σ x) = (σ y) := by grind
  clear eq6724
  have eq6800 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq6725
       grind)
    | exact superpose eq6725 eq16
    | exact resolve eq16 eq6725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq6801 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq6725
       grind)
    | exact superpose eq6725 eq10
    | exact resolve eq10 eq6725
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6725
  have eq6858 : x = y := by
    first
    | (have i₁ := eq6801
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq6801
    | exact resolve eq6801 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6801
  have eq6859 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6800
       have i₂ := eq22 x
       grind)
    | exact superpose eq22 eq6800
    | exact resolve eq6800 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6800
  have eq6860 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq6859
       have i₂ := eq6858
       grind)
    | exact superpose eq6858 eq6859
    | exact resolve eq6859 eq6858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6858 eq6859
  have eq6861 : False := by grind
  exact eq6861
