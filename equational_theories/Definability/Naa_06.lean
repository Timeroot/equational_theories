import equational_theories.Definability.AutBox2
import equational_theories.Superposition

open FirstOrder FirstOrder.Language Law Law.MagmaLaw FreeMagma

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-- `Equation3873`: `x ◇ x = (x ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = m(Y,X) then m(X,Y) else if m(Y,X) = X then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_pyx_pyx_x_pxy_x_pyx_Equation3873 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3873 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3873.models_iff G M).mp hM
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
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X0) = X0 ∨ (M.op X0 X1) = (M.op X1 X0) := by
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
  have eq86 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
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
  have eq313 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X1) (σ X0)
       have i₂ := eq86 X0 X1
       grind)
    | (have i₁ := eq12 (σ X0) (σ X1)
       have i₂ := eq86 X0 X1
       grind)
    | exact superpose eq86 eq12
    | (have j1 := eq86 X0 X1
       grind)
    | (have r₁ := eq12 (σ X1) (σ X0)
       have r₂ := eq86 X0 X1
       grind)
    | (have r₁ := eq12 (σ X0) (σ X1)
       have r₂ := eq86 X0 X1
       grind)
    | exact resolve eq12 eq86
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86
  have eq327 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq313 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq313
  have eq334 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) ∨ (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq327 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq327
    | (have j0 := eq327 X0 X1
       grind)
    | exact resolve eq327 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq327
  have eq335 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq334 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq334
  have eq683 : ∀ X0 X1 : G, (σ (k (τ X0) X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq335 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq335
    | exact resolve eq335 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq690 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq335 x y
       grind)
    | exact superpose eq335 eq16
    | (have j1 := eq335 x y
       grind)
    | exact resolve eq16 eq335
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq711 : ∀ X0 X1 : G, (σ X1) ≠ (σ (k X1 X0)) ∨ (σ X1) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have j0 := eq335 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq335
  have eq725 : ∀ X0 X1 : G, (k X0 (σ X1)) = (M.op (σ X1) X0) ∨ (M.op (σ X1) X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq683 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq683
    | (have j0 := eq683 X0 X1
       grind)
    | exact resolve eq683 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq683
  have eq1017 : ∀ X0 X1 : G, (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq725 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq725
    | exact resolve eq725 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq725
  have eq1070 : ∀ X0 X1 : G, (M.op (τ X0) X1) = X1 ∨ (k (σ X1) X0) = (σ (M.op (τ X0) X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X0 X1
       have i₂ := eq1017 (τ X0) X1
       grind)
    | exact superpose eq1017 eq18
    | (have j1 := eq1017 (τ X0) X1
       grind)
    | exact resolve eq18 eq1017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq1017
  have eq1676 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1070 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq1070
    | exact resolve eq1070 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1070
  have eq1751 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq1676 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq1676
    | (have j0 := eq1676 X0 X1
       grind)
    | exact resolve eq1676 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1676
  have eq2264 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq690
       have i₂ := eq1751 x y
       grind)
    | exact superpose eq1751 eq690
    | (have j1 := eq1751 (σ x) (σ y)
       grind)
    | (have r₁ := eq690
       have r₂ := eq1751 x y
       grind)
    | exact resolve eq690 eq1751
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq690
  have eq2265 : y = (M.op x y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2264
  have eq2269 : y ≠ y ∨ y = (k y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq13 y x
       have i₂ := eq2265
       grind)
    | exact superpose eq2265 eq13
    | (have j0 := eq13 y x
       grind)
    | (have r₁ := eq13 y x
       have r₂ := eq2265
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq2265
       grind)
    | exact resolve eq13 eq2265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2278 : y = (k y x) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq2269
  have eq5658 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq711 x y
       have i₂ := eq2278
       grind)
    | exact superpose eq2278 eq711
    | (have j0 := eq711 x y
       grind)
    | exact resolve eq711 eq2278
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2278
  have eq5679 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ y = (M.op y x) := by grind
  clear eq5658
  have eq5680 : y = (M.op y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5679
  have eq5687 : y ≠ (M.op x y) ∨ y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq12 y x
       have i₂ := eq5680
       grind)
    | exact superpose eq5680 eq12
    | exact resolve eq12 eq5680
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5680
  have eq5720 : y = (k y x) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq5687
       have r₂ := eq2265
       grind)
    | exact resolve eq5687 eq2265
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2265 eq5687
  have eq5816 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq711 x y
       have i₂ := eq5720
       grind)
    | exact superpose eq5720 eq711
    | (have j0 := eq711 x y
       grind)
    | exact resolve eq711 eq5720
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq711 eq5720
  have eq5837 : (σ y) ≠ (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5816
  have eq5838 : (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq5837
  have eq5846 : (σ (M.op x y)) ≠ (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq5838
       grind)
    | exact superpose eq5838 eq16
    | exact resolve eq16 eq5838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5851 : (σ y) ≠ (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by
    first
    | (have i₁ := eq13 (σ y) (σ x)
       have i₂ := eq5838
       grind)
    | exact superpose eq5838 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | (have r₁ := eq13 (σ y) (σ x)
       have r₂ := eq5838
       grind)
    | exact resolve eq13 eq5838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5881 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (M.op (σ y) (σ x)) := by grind
  clear eq5851
  have eq5895 : (σ y) = (M.op (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq5881
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq5881
    | exact resolve eq5881 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5881
  have eq6870 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq12 (σ y) (σ x)
       have i₂ := eq5895
       grind)
    | exact superpose eq5895 eq12
    | exact resolve eq12 eq5895
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5895
  have eq6920 : (σ y) = (k (σ y) (σ x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have r₁ := eq6870
       have r₂ := eq5838
       grind)
    | exact resolve eq6870 eq5838
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5838 eq6870
  have eq6943 : (σ y) = (σ (k y x)) ∨ (σ y) = (σ (k y x)) := by
    first
    | (have i₁ := eq6920
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq6920
    | exact resolve eq6920 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6920
  have eq6944 : (σ y) = (σ (k y x)) := by grind
  clear eq6943
  have eq7118 : (σ (M.op x y)) = (σ y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1751 x y
       have i₂ := eq6944
       grind)
    | exact superpose eq6944 eq1751
    | (have j0 := eq1751 x y
       grind)
    | exact resolve eq1751 eq6944
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1751 eq6944
  have eq7185 : y = (M.op x y) := by
    first
    | (have r₁ := eq7118
       have r₂ := eq5846
       grind)
    | exact resolve eq7118 eq5846
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7118
  have eq7395 : (σ y) ≠ (σ y) := by
    first
    | (have i₁ := eq5846
       have i₂ := eq7185
       grind)
    | exact superpose eq7185 eq5846
    | exact resolve eq5846 eq7185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5846 eq7185
  have eq7430 : False := by grind
  exact eq7430

/-- `Equation3874`: `x ◇ x = (x ◇ (y ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,Y) then m(Y,X) else if m(X,Y) = m(Y,X) then m(Y,X) else m(X,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyy_pxy_pyx_pyx_pyx_pxy_Equation3874 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) Law3874 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3874.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b b ∨ M.op a b = M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X1 X0) ≠ (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X0) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
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
  have eq68 : ∀ X0 : G, (σ (M.op (τ X0) (τ X0))) = (k (σ (τ X0)) X0) := by
    intro X0
    first
    | (have i₁ := eq18 X0 (τ X0)
       have i₂ := eq61 (τ X0)
       grind)
    | exact superpose eq61 eq18
    | exact resolve eq18 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq71 : ∀ X0 : G, (k X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq68 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq68
    | exact resolve eq68 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68
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
  clear eq64
  have eq79 : ∀ X0 : G, (M.op X0 X0) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq61 X0
       grind)
    | exact superpose eq61 eq71
    | exact resolve eq71 eq61
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq61 eq71
  have eq85 : ∀ X0 X1 : G, (M.op X1 X1) ≠ (σ (M.op X0 X0)) ∨ (k X1 (σ X0)) = (M.op (σ X0) X1) := by
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
  have eq317 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq85 X1 (σ X0)
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq85
    | (have j0 := eq85 X1 (σ X0)
       grind)
    | (have r₁ := eq85 X0 (σ X0)
       have r₂ := eq75 X0
       grind)
    | exact resolve eq85 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq85
  have eq324 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq317 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq317
    | (have j0 := eq317 X0 X1
       grind)
    | exact resolve eq317 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq317
  have eq1320 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X1) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq13 X0 X1
       have j1 := eq12 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq12 X0 X1
       grind)
    | (have r₁ := eq13 X1 X0
       have r₂ := eq12 X0 X1
       grind)
    | exact resolve eq13 eq12
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1360 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X1)) := by
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
  have eq1419 : ∀ X0 X1 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X1 X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1360 X0 X1
       have i₂ := eq75 X1
       grind)
    | exact superpose eq75 eq1360
    | (have j0 := eq1360 X0 X1
       grind)
    | exact resolve eq1360 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1360
  have eq1447 : ∀ X0 X1 : G, (M.op (σ X1) (σ X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1419 X0 X1
       have i₂ := eq75 X0
       grind)
    | exact superpose eq75 eq1419
    | (have j0 := eq1419 X0 X1
       grind)
    | exact resolve eq1419 eq75
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75 eq1419
  have eq16083 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) ≠ (M.op (σ X0) (σ X1)) ∨ (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq1320 (σ X0) (σ X1)
       have i₂ := eq1447 X0 X1
       grind)
    | (have i₁ := eq1320 (σ X1) (σ X0)
       have i₂ := eq1447 X0 X1
       grind)
    | exact superpose eq1447 eq1320
    | (have j1 := eq1447 X0 X1
       grind)
    | (have r₁ := eq1320 (σ X0) (σ X1)
       have r₂ := eq1447 X0 X1
       grind)
    | (have r₁ := eq1320 (σ X1) (σ X0)
       have r₂ := eq1447 X0 X1
       grind)
    | exact resolve eq1320 eq1447
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1320 eq1447
  have eq16089 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq16083 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16083
  have eq16093 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16089 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq16089
    | (have j0 := eq16089 X0 X1
       grind)
    | exact resolve eq16089 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16089
  have eq16094 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X0 X0)) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq16093 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16093
  have eq16144 : ∀ X0 X1 : G, (σ (k X1 (τ X0))) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16094 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16094
    | (have j0 := eq16094 (τ X0) X1
       grind)
    | exact resolve eq16094 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16158 : (σ (M.op x y)) ≠ (σ (k x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq16094 x y
       grind)
    | exact superpose eq16094 eq16
    | (have j1 := eq16094 x y
       grind)
    | exact resolve eq16 eq16094
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16094
  have eq16180 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (σ (M.op (τ X0) (τ X0))) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16144 X0 X1
       have i₂ := eq18 X0 X1
       grind)
    | exact superpose eq18 eq16144
    | (have j0 := eq16144 X0 X1
       grind)
    | exact resolve eq16144 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq16144
  have eq16194 : ∀ X0 X1 : G, (k (σ X1) X0) = (M.op (σ X1) X0) ∨ (M.op X0 X0) = (σ (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16180 X0 X1
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq16180
    | (have j0 := eq16180 X0 X1
       grind)
    | exact resolve eq16180 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16180
  have eq16215 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X1 X1) = (σ (M.op (τ X0) (τ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq16194 X0 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq16194
    | (have j0 := eq16194 X1 (τ X0)
       grind)
    | exact resolve eq16194 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16194
  have eq16386 : ∀ X0 X1 : G, (k X0 X1) = (M.op X0 X1) ∨ (M.op X0 X0) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq16215 X0 X1
       have i₂ := eq79 X0
       grind)
    | exact superpose eq79 eq16215
    | (have j0 := eq16215 X0 X1
       grind)
    | exact resolve eq16215 eq79
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq79 eq16215
  have eq17034 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq16158
       have i₂ := eq16386 x y
       grind)
    | exact superpose eq16386 eq16158
    | (have j1 := eq16386 x y
       grind)
    | exact resolve eq16158 eq16386
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16158 eq16386
  have eq17039 : (σ (M.op x x)) = (σ (M.op y y)) ∨ (M.op x x) = (M.op y y) := by grind
  clear eq17034
  have eq17072 : (M.op y y) = (τ (σ (M.op x x))) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq17039
       grind)
    | exact superpose eq17039 eq10
    | exact resolve eq10 eq17039
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17039
  have eq17197 : (M.op x x) = (M.op y y) ∨ (M.op x x) = (M.op y y) := by
    first
    | (have i₁ := eq17072
       have i₂ := eq10 (M.op x x)
       grind)
    | exact superpose eq10 eq17072
    | exact resolve eq17072 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17072
  have eq17198 : (M.op x x) = (M.op y y) := by grind
  clear eq17197
  have eq17199 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op x x) ∨ (k y X0) = (M.op X0 y) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq17198
       grind)
    | exact superpose eq17198 eq12
    | (have j0 := eq12 X0 x
       grind)
    | (have r₁ := eq12 x y
       have r₂ := eq17198
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq17198
       grind)
    | exact resolve eq12 eq17198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq17207 : ∀ X0 : G, (σ (M.op X0 X0)) ≠ (σ (M.op x x)) ∨ (σ (k y X0)) = (M.op (σ X0) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq324 y X0
       have i₂ := eq17198
       grind)
    | exact superpose eq17198 eq324
    | (have j0 := eq324 X0 x
       grind)
    | exact resolve eq324 eq17198
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq324 eq17198
  have eq17279 : (M.op x y) = (k y x) := by
    first
    | (have j0 := eq17199 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17199
  have eq19361 : (M.op (σ x) (σ y)) = (σ (k y x)) := by
    first
    | (have j0 := eq17207 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17207
  have eq19364 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq19361
       have i₂ := eq17279
       grind)
    | exact superpose eq17279 eq19361
    | exact resolve eq19361 eq17279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17279 eq19361
  have eq19370 : False := by grind
  exact eq19370

/-- `Equation3880`: `x ◇ x = (y ◇ (x ◇ y)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,Y) = Y then m(Y,X) else if m(X,Y) = m(Y,X) then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyy_y_pxy_pyx_pyx_pxy_pyx_Equation3880 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3880 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 1)) (Lf 1) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3880.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b b ≠ b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b b = b ∨ M.op a b ≠ M.op b a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op a b) (M.op b a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b b = b ∨ M.op a b = M.op b a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b b) (b)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) ≠ (M.op X1 X0) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (M.op X0 X1) = (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
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
  have eq263 : ∀ X0 X1 X2 : G, X0 ≠ X0 ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X2 X0) ≠ (M.op X0 X2) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X1 X0
       have i₂ := eq13 X2 X0
       grind)
    | exact superpose eq13 eq12
    | (have j0 := eq12 X1 X0
       have j1 := eq13 X2 X0
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq12 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq264 : ∀ X0 X1 X2 : G, (M.op X2 X0) ≠ (M.op X0 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (k X2 X0) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq263 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq263
  have eq1870 : ∀ X0 X1 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq264 X0 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1931 : ∀ X0 : G, (M.op X0 X0) ≠ (M.op X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1870 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1870
  have eq1932 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq1931 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1931
  have eq2085 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq31 X0 X0
       have i₂ := eq1932 (τ X0)
       grind)
    | exact superpose eq1932 eq31
    | exact resolve eq31 eq1932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31
  have eq2132 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq2085 X0
       have i₂ := eq1932 X0
       grind)
    | exact superpose eq1932 eq2085
    | exact resolve eq2085 eq1932
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1932 eq2085
  have eq2309 : ∀ X0 X1 : G, (τ X0) = (τ (M.op X0 X0)) ∨ (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq14 X1 (τ X0)
       have i₂ := eq2132 X0
       grind)
    | exact superpose eq2132 eq14
    | (have j0 := eq14 (τ X0) X1
       grind)
    | exact resolve eq14 eq2132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2311 : ∀ X0 X1 : G, (τ X0) ≠ (τ (M.op X0 X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X1 (τ X0)
       have i₂ := eq2132 X0
       grind)
    | exact superpose eq2132 eq12
    | (have j0 := eq12 X1 (τ X0)
       grind)
    | exact resolve eq12 eq2132
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2132
  have eq2314 : ∀ X0 X1 : G, (M.op (τ X0) X1) = (M.op X1 (τ X0)) ∨ (k X1 (τ X0)) = (M.op (τ X0) X1) := by
    intro X0 X1
    first
    | (have j0 := eq2309 X0 X1
       have j1 := eq2311 X0 X1
       grind)
    | (have r₁ := eq2309 X0 X1
       have r₂ := eq2311 X0 X1
       grind)
    | exact resolve eq2309 eq2311
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2309 eq2311
  have eq2430 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq2314 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq2314
    | exact resolve eq2314 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2314
  have eq2473 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = (k X1 X0) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq264 X1 X1 X0
       have i₂ := eq2430 X0 X1
       grind)
    | (have i₁ := eq264 X0 X1 X1
       have i₂ := eq2430 X0 X1
       grind)
    | exact superpose eq2430 eq264
    | (have j0 := eq264 X0 X2 X2
       have j1 := eq2430 X0 X2
       grind)
    | (have r₁ := eq264 X1 X1 X0
       have r₂ := eq2430 X0 X1
       grind)
    | (have r₁ := eq264 X0 X1 X1
       have r₂ := eq2430 X0 X1
       grind)
    | exact resolve eq264 eq2430
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq264 eq2430
  have eq2479 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2473 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2473
  have eq2480 : ∀ X0 X1 X2 : G, (k X2 X0) = (M.op X0 X2) ∨ (M.op X0 X1) = (k X1 X0) := by
    intro X0 X1 X2
    first
    | (have j0 := eq2479 X0 X2 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2479
  have eq2583 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X1 X0) ∨ (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2480 X1 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2480
  have eq2584 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) := by
    intro X0 X1
    first
    | (have j0 := eq2583 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2583
  have eq2623 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq15 X1 X0
       have i₂ := eq2584 (σ X1) (σ X0)
       grind)
    | exact superpose eq2584 eq15
    | exact resolve eq15 eq2584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2738 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (σ (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2623 X0 X1
       have i₂ := eq2584 X1 X0
       grind)
    | exact superpose eq2584 eq2623
    | exact resolve eq2623 eq2584
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2584 eq2623
  have eq3880 : (σ (M.op x y)) ≠ (σ (M.op x y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq2738 x y
       grind)
    | exact superpose eq2738 eq16
    | (have r₁ := eq16
       have r₂ := eq2738 x y
       grind)
    | exact resolve eq16 eq2738
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2738
  have eq3896 : False := by grind
  exact eq3896

/-- `Equation3897`: `x ◇ x = (y ◇ (z ◇ x)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = m(Y,X) then m(X,X) else if X = Y then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_pyx_x_y_pxx_pxy_pyx_Equation3897 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3897 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3897.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ M.op b a ∨ k a b = M.op a a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = M.op b a ∨ a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
      (fun hg ↦ (eq_or_ne (a) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = M.op b a ∨ a = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (M.op b a)).imp id
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
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ (M.op X0 X0) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ X0 = X1 ∨ (M.op X0 X0) = (M.op X1 X0) := by
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
  clear eq18
  have eq32 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
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
  clear eq23
  have eq65 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq12 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq69 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ X0) (σ X0)) := by
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
  have eq71 : ∀ X0 : G, (τ (k X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq32 X0 X0
       have i₂ := eq65 (τ X0)
       grind)
    | exact superpose eq65 eq32
    | exact resolve eq32 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq78 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq71 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq71
    | exact resolve eq71 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq71
  have eq80 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq69 X0
       have i₂ := eq65 X0
       grind)
    | exact superpose eq65 eq69
    | exact resolve eq69 eq65
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq65 eq69
  have eq96 : ∀ X0 X1 : G, (σ (M.op X0 X0)) ≠ (M.op X1 (σ X0)) ∨ (k (σ X0) X1) = (σ (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (σ X0) X1
       have i₂ := eq80 X0
       grind)
    | exact superpose eq80 eq12
    | exact resolve eq12 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq905 : ∀ X0 X1 : G, (k (σ X1) X0) = (σ (M.op (τ X0) X1)) ∨ (τ X0) = X1 ∨ (M.op X1 X1) = (M.op (τ X0) X1) := by
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
  clear eq19
  have eq918 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) ∨ (M.op (σ X1) (σ X1)) = (M.op (σ X0) (σ X1)) := by
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
  have eq948 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq918 X0 X1
       have i₂ := eq80 X1
       grind)
    | exact superpose eq80 eq918
    | (have j0 := eq918 X0 X1
       grind)
    | exact resolve eq918 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq918
  have eq3634 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq948 x y
       grind)
    | exact superpose eq948 eq16
    | (have j1 := eq948 x y
       grind)
    | exact resolve eq16 eq948
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3654 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (σ (M.op X1 X1)) = (M.op (σ X0) (σ X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq948 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq948
  have eq9192 : ∀ X0 X1 : G, (k (σ X1) (σ X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq905 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq905
    | exact resolve eq905 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq905
  have eq9279 : ∀ X0 X1 : G, (σ (k X1 X0)) = (σ (M.op X0 X1)) ∨ X0 = X1 ∨ (M.op X0 X1) = (M.op X1 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq9192 X0 X1
       have i₂ := eq15 X1 X0
       grind)
    | exact superpose eq15 eq9192
    | (have j0 := eq9192 X0 X1
       grind)
    | exact resolve eq9192 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9192
  have eq15930 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq3634
       have i₂ := eq9279 x y
       grind)
    | exact superpose eq9279 eq3634
    | (have j1 := eq9279 x y
       grind)
    | (have r₁ := eq3634
       have r₂ := eq9279 x y
       grind)
    | (have r₁ := eq3634
       have r₂ := eq9279 (σ (M.op x y)) (σ (k y x))
       grind)
    | (have r₁ := eq3634
       have r₂ := eq9279 (σ (k y x)) (σ (M.op x y))
       grind)
    | exact resolve eq3634 eq9279
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq9279
  have eq15931 : x = y ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq15930
  have eq19071 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (M.op (τ X0) (τ X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq3654 (τ X1) (τ X0)
       have i₂ := eq32 X1 X0
       grind)
    | exact superpose eq32 eq3654
    | (have j0 := eq3654 (τ X1) (τ X0)
       grind)
    | exact resolve eq3654 eq32
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq32
  have eq19177 : ∀ X0 X1 : G, (σ (τ (k X0 X1))) ≠ (σ (τ (M.op X0 X0))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19071 X0 X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq19071
    | (have j0 := eq19071 X0 X1
       grind)
    | exact resolve eq19071 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19071
  have eq19254 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (σ (τ (k X0 X1))) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19177 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq19177
    | (have j0 := eq19177 X0 X1
       grind)
    | exact resolve eq19177 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19177
  have eq19326 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) (σ (τ X0))) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19254 X0 X1
       have i₂ := eq11 (k X0 X1)
       grind)
    | exact superpose eq11 eq19254
    | (have j0 := eq19254 X0 X1
       grind)
    | exact resolve eq19254 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19254
  have eq19379 : ∀ X0 X1 : G, (σ (M.op (τ X0) (τ X0))) = (M.op (σ (τ X1)) X0) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19326 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19326
    | (have j0 := eq19326 X0 X1
       grind)
    | exact resolve eq19326 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19326
  have eq19427 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (M.op (τ X0) (τ X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19379 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq19379
    | (have j0 := eq19379 X0 X1
       grind)
    | exact resolve eq19379 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19379
  have eq19467 : ∀ X0 X1 : G, (M.op X1 X0) = (σ (τ (M.op X0 X0))) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19427 X0 X1
       have i₂ := eq78 X0
       grind)
    | exact superpose eq78 eq19427
    | (have j0 := eq19427 X0 X1
       grind)
    | exact resolve eq19427 eq78
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78 eq19427
  have eq19500 : ∀ X0 X1 : G, (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ (k X0 X1) ∨ (σ (τ X0)) = (σ (τ X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq19467 X0 X1
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq19467
    | (have j0 := eq19467 X0 X1
       grind)
    | exact resolve eq19467 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19467
  have eq19527 : ∀ X0 X1 : G, (σ (τ X0)) = X1 ∨ (M.op X0 X0) = (M.op X1 X0) ∨ (M.op X0 X0) ≠ (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq19500 X0 X1
       have i₂ := eq11 X1
       grind)
    | exact superpose eq11 eq19500
    | (have j0 := eq19500 X0 X1
       grind)
    | exact resolve eq19500 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19500
  have eq19544 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (k X0 X1) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq19527 X0 X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq19527
    | (have j0 := eq19527 X0 X1
       grind)
    | exact resolve eq19527 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19527
  have eq37602 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq15931
       grind)
    | exact superpose eq15931 eq16
    | exact resolve eq16 eq15931
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq15931
  have eq37603 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq37602
       have r₂ := eq80 x
       grind)
    | exact resolve eq37602 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37602
  have eq37608 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq96 y (σ x)
       have i₂ := eq37603
       grind)
    | exact superpose eq37603 eq96
    | (have j0 := eq96 y (σ x)
       grind)
    | (have r₁ := eq96 y (σ x)
       have r₂ := eq37603
       grind)
    | exact resolve eq96 eq37603
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37603
  have eq37614 : (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) := by grind
  clear eq37608
  have eq37621 : (M.op x y) = (M.op y y) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq37614
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq37614
    | exact resolve eq37614 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37614
  have eq37625 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ (M.op x y) = (k y X0) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    intro X0
    first
    | (have i₁ := eq12 y x
       have i₂ := eq37621
       grind)
    | exact superpose eq37621 eq12
    | (have r₁ := eq12 y x
       have r₂ := eq37621
       grind)
    | exact resolve eq12 eq37621
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37621
  have eq181845 : (M.op x y) = (k y x) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have j0 := eq37625 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37625
  have eq181879 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq3634
       have i₂ := eq181845
       grind)
    | exact superpose eq181845 eq3634
    | exact resolve eq3634 eq181845
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3634 eq181845
  have eq181915 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) := by grind
  clear eq181879
  have eq181916 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) := by grind
  clear eq181915
  have eq181921 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have j1 := eq3654 x y
       grind)
    | (have r₁ := eq181916
       have r₂ := eq3654 x y
       grind)
    | exact resolve eq181916 eq3654
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3654 eq181916
  have eq181923 : (σ (M.op x y)) ≠ (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq181921
       grind)
    | exact superpose eq181921 eq16
    | exact resolve eq16 eq181921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181931 : (σ (M.op y y)) ≠ (σ (M.op y y)) ∨ (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq96 y (σ x)
       have i₂ := eq181921
       grind)
    | exact superpose eq181921 eq96
    | (have j0 := eq96 y (σ x)
       grind)
    | (have r₁ := eq96 y (σ x)
       have r₂ := eq181921
       grind)
    | exact resolve eq96 eq181921
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96 eq181921
  have eq181953 : (σ (M.op y y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by grind
  clear eq181931
  have eq181967 : (σ x) = (σ y) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq181953
       have i₂ := eq15 y x
       grind)
    | exact superpose eq15 eq181953
    | exact resolve eq181953 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181953
  have eq181975 : y = (τ (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq181967
       grind)
    | exact superpose eq181967 eq10
    | exact resolve eq10 eq181967
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181967
  have eq182241 : x = y ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq181975
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq181975
    | exact resolve eq181975 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181975
  have eq182243 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq182241
       grind)
    | exact superpose eq182241 eq16
    | exact resolve eq16 eq182241
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182241
  have eq182244 : (σ (k y x)) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq182243
       have r₂ := eq80 x
       grind)
    | exact resolve eq182243 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182243
  have eq182272 : (k y x) = (τ (σ (M.op y y))) := by
    first
    | (have i₁ := eq10 (k y x)
       have i₂ := eq182244
       grind)
    | exact superpose eq182244 eq10
    | exact resolve eq10 eq182244
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182244
  have eq182539 : (k y x) = (M.op y y) := by
    first
    | (have i₁ := eq182272
       have i₂ := eq10 (M.op y y)
       grind)
    | exact superpose eq10 eq182272
    | exact resolve eq182272 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182272
  have eq182598 : (M.op y y) ≠ (M.op y y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq19544 y x
       have i₂ := eq182539
       grind)
    | exact superpose eq182539 eq19544
    | (have j0 := eq19544 y x
       grind)
    | (have r₁ := eq19544 y x
       have r₂ := eq182539
       grind)
    | exact resolve eq19544 eq182539
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19544 eq182539
  have eq182665 : x = y ∨ (M.op x y) = (M.op y y) := by grind
  clear eq182598
  have eq182669 : (σ (M.op x x)) ≠ (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq182665
       grind)
    | exact superpose eq182665 eq16
    | exact resolve eq16 eq182665
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182665
  have eq182672 : (M.op x y) = (M.op y y) := by
    first
    | (have r₁ := eq182669
       have r₂ := eq80 x
       grind)
    | exact resolve eq182669 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182669
  have eq182673 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq181923
       have i₂ := eq182672
       grind)
    | exact superpose eq182672 eq181923
    | exact resolve eq181923 eq182672
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181923 eq182672
  have eq182798 : (σ x) = (σ y) := by grind
  clear eq182673
  have eq182803 : (σ (M.op x y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq182798
       grind)
    | exact superpose eq182798 eq16
    | exact resolve eq16 eq182798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq182804 : y = (τ (σ x)) := by
    first
    | (have i₁ := eq10 y
       have i₂ := eq182798
       grind)
    | exact superpose eq182798 eq10
    | exact resolve eq10 eq182798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182798
  have eq183160 : x = y := by
    first
    | (have i₁ := eq182804
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq182804
    | exact resolve eq182804 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq182804
  have eq183161 : (σ (M.op x y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq182803
       have i₂ := eq80 x
       grind)
    | exact superpose eq80 eq182803
    | exact resolve eq182803 eq80
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq80 eq182803
  have eq183187 : (σ (M.op x x)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq183161
       have i₂ := eq183160
       grind)
    | exact superpose eq183160 eq183161
    | exact resolve eq183161 eq183160
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq183160 eq183161
  have eq183188 : False := by grind
  exact eq183188

/-- `Equation3921`: `x ◇ y = (x ◇ (x ◇ z)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if X = Y then m(X,X) else if m(X,X) = m(Y,X) then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_x_y_pxx_pyx_pxx_x_pyx_Equation3921 :
    AutBox.GuardAut2 (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3921 := by
  classical
  refine AutBox.guardAut2_of (Lf 0) (Lf 1) ((Lf 0) ⋆ (Lf 0)) ((Lf 1) ⋆ (Lf 0)) ((Lf 0) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3921.models_iff G M).mp hM
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
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X0) ∨ (M.op X0 X0) = (M.op X1 X0) ∨ X0 = X1 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X0) ≠ (M.op X1 X0) ∨ X0 = X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, X0 ≠ X1 ∨ (k X0 X1) = (M.op X0 X0) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X0 X2)) X1) := by
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
  have eq53 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x (M.op x y)) X0) := by
    intro X0
    first
    | (have i₁ := eq14 x X0 y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq14
    | (have j0 := eq14 x X0 y
       grind)
    | exact resolve eq14 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq54 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (M.op (σ x) (σ y))) X0) := by
    intro X0
    first
    | exact superpose eq27 eq14
    | (have j0 := eq14 (σ x) X0 (σ y)
       grind)
    | exact resolve eq14 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq72 : (M.op x x) = (τ (M.op (σ x) (σ x))) := by
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
  have eq73 : ∀ X0 X1 X2 : G, (M.op X0 (M.op X0 (M.op X0 X1))) ≠ (M.op X2 (M.op X0 (M.op X0 X1))) ∨ (M.op X0 (M.op X0 X1)) = X2 ∨ (M.op X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 X1)) X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 (M.op X0 (M.op X0 X1)) X2
       have i₂ := eq14 X0 (M.op X0 (M.op X0 X1)) X1
       grind)
    | exact superpose eq14 eq12
    | (have j0 := eq12 (M.op X0 (M.op X0 X1)) X2
       grind)
    | (have r₁ := eq12 X1 (M.op X1 (M.op X1 X2))
       have r₂ := eq14 X1 X1 X2
       grind)
    | (have r₁ := eq12 (M.op X0 (M.op X0 X2)) X0
       have r₂ := eq14 X0 (M.op X0 (M.op X0 X2)) X2
       grind)
    | exact resolve eq12 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq79 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
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
  have eq91 : (σ (k y x)) = (k (σ y) (σ x)) := by
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
  have eq92 : (σ (k y y)) = (k (σ y) (σ y)) := by
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
  have eq96 : (M.op (σ y) (σ y)) = (σ (k y y)) := by grind
  clear eq92
  have eq97 : (M.op (σ y) (σ y)) = (σ (M.op y y)) := by grind
  clear eq96
  have eq98 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq91
       have i₂ := eq11 y x
       grind)
    | exact superpose eq11 eq91
    | (have j1 := eq11 y x
       grind)
    | exact resolve eq91 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq104 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
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
  have eq105 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq21 eq104
    | exact resolve eq104 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104
  have eq106 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have i₁ := eq105
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq105
    | exact resolve eq105 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq105
  have eq121 : (σ (k (M.op x y) (M.op x y))) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq21 eq38
    | (have j0 := eq38 (M.op x y)
       grind)
    | exact resolve eq38 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq124 : (σ (k (M.op x y) (M.op x y))) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq121
  have eq125 : (M.op (σ (M.op x y)) (σ (M.op x y))) = (σ (M.op (M.op x y) (M.op x y))) := by grind
  clear eq124
  have eq131 : (M.op y y) = (τ (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq16 (M.op y y)
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq16
    | exact resolve eq16 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq164 : (M.op (M.op x y) (M.op x y)) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) := by
    first
    | exact superpose eq125 eq16
    | exact resolve eq16 eq125
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq660 : ∀ X0 X1 : G, (σ (k X0 X1)) = (M.op (σ X1) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ X1) (σ X0)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have i₁ := eq79 X0 X1
       have i₂ := eq45 X0
       grind)
    | exact superpose eq45 eq79
    | (have j0 := eq79 X0 X1
       grind)
    | exact resolve eq79 eq45
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq45 eq79
  have eq717 : ∀ X0 : G, (σ (k X0 x)) = (M.op (σ x) (σ X0)) ∨ (σ (M.op X0 X0)) = (M.op (σ x) (σ X0)) ∨ (σ X0) = (σ x) := by
    intro X0
    first
    | (have i₁ := eq660 X0 x
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq660
    | (have j0 := eq660 X0 x
       grind)
    | exact resolve eq660 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq742 : ∀ X0 X1 : G, (σ (k X1 X0)) ≠ (σ (M.op X1 X1)) ∨ (M.op (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (σ X0) = (σ X1) := by
    intro X0 X1
    first
    | (have j0 := eq660 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq660
  have eq843 : ∀ X0 X1 : G, (M.op X0 (M.op X0 X1)) = (k (M.op X0 (M.op X0 X1)) X0) ∨ (M.op X0 (M.op X0 X1)) = X0 := by
    intro X0 X1
    first
    | (have j0 := eq73 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq73
  have eq3685 : (M.op x (M.op x y)) = (k (M.op x (M.op x y)) x) ∨ x = (M.op x (M.op x y)) := by
    first
    | (have i₁ := eq843 x y
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq843
    | (have j0 := eq843 x y
       grind)
    | exact resolve eq843 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq843
  have eq5005 : (M.op (σ x) (σ y)) = (σ (k y x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq717 y
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq717
    | (have j0 := eq717 y
       grind)
    | exact resolve eq717 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq717
  have eq5016 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5005
       have i₂ := eq91
       grind)
    | exact superpose eq91 eq5005
    | exact resolve eq5005 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5005
  have eq5035 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq5016
    | exact resolve eq5016 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5016
  have eq5043 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq5035
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq5035
    | exact resolve eq5035 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5035
  have eq5049 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq5043
    | exact resolve eq5043 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5043
  have eq10086 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq106 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq106
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq10087 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq10086
    | exact resolve eq10086 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10086
  have eq10098 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | (have r₁ := eq10087
       have r₂ := eq28
       grind)
    | exact resolve eq10087 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10087
  have eq10102 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq10098
    | exact resolve eq10098 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10098
  have eq10221 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op X0 (σ y)) ∨ (σ y) = X0 ∨ (σ y) = (k (σ y) X0) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    intro X0
    first
    | exact superpose eq10102 eq12
    | (have j0 := eq12 (σ y) X0
       grind)
    | (have r₁ := eq12 (σ y) (σ x)
       have r₂ := eq10102
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq10102
       grind)
    | exact resolve eq12 eq10102
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10102
  have eq16099 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq27 eq10221
    | (have j0 := eq10221 (σ x)
       grind)
    | (have r₁ := eq10221 (σ x)
       have r₂ := eq27
       grind)
    | exact resolve eq10221 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq10221
  have eq16100 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ (σ y) = (k (σ y) (σ x)) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq16099
  have eq16101 : (σ y) = (k (σ y) (σ x)) ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by grind
  clear eq16100
  have eq16113 : (σ (M.op x y)) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y ∨ (σ x) = (σ y) ∨ (M.op x y) = (M.op y y) ∨ x = y := by
    first
    | exact superpose eq16101 eq106
    | exact resolve eq106 eq16101
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq106 eq16101
  have eq16126 : (M.op x y) = (M.op y y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq16113
  have eq16146 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq97
       have i₂ := eq16126
       grind)
    | exact superpose eq16126 eq97
    | exact resolve eq97 eq16126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq16153 : ∀ X0 : G, (M.op x y) ≠ (M.op X0 y) ∨ y = X0 ∨ y = (k y X0) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    intro X0
    first
    | (have i₁ := eq12 y X0
       have i₂ := eq16126
       grind)
    | exact superpose eq16126 eq12
    | (have j0 := eq12 y X0
       grind)
    | (have r₁ := eq12 y x
       have r₂ := eq16126
       grind)
    | exact resolve eq12 eq16126
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16126
  have eq16177 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq21 eq16146
    | exact resolve eq16146 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16146
  have eq96767 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq16153 x
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq16153
    | (have j0 := eq16153 x
       grind)
    | (have r₁ := eq16153 x
       have r₂ := eq19
       grind)
    | exact resolve eq16153 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16153
  have eq96770 : (M.op x y) ≠ (M.op x y) ∨ x = y ∨ y = (k y x) ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq96767
  have eq96771 : y = (k y x) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by grind
  clear eq96770
  have eq96788 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq91
       have i₂ := eq96771
       grind)
    | exact superpose eq96771 eq91
    | exact resolve eq91 eq96771
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91 eq96771
  have eq96878 : (σ y) = (k (σ y) (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | (have i₁ := eq96788
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq96788
    | exact resolve eq96788 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96788
  have eq96940 : (σ y) = (M.op (σ x) (σ y)) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq96878 eq5049
    | exact resolve eq5049 eq96878
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5049 eq96878
  have eq96997 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by grind
  clear eq96940
  have eq97041 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq96997 eq16177
    | exact resolve eq16177 eq96997
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96997
  have eq97160 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq97041
  have eq97177 : (σ y) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq97160
       have r₂ := eq28
       grind)
    | exact resolve eq97160 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97160
  have eq97183 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq97177 eq54
    | exact resolve eq54 eq97177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq54
  have eq97222 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (M.op (σ x) (σ y)) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq27 eq97183
    | (have j0 := eq97183 X0
       grind)
    | exact resolve eq97183 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97183
  have eq97230 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | exact superpose eq97177 eq97222
    | exact resolve eq97222 eq97177
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97177 eq97222
  have eq97275 : ∀ X0 : G, (M.op (σ x) X0) = (M.op (σ y) X0) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    intro X0
    first
    | (have j0 := eq97230 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97230
  have eq97328 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y ∨ (σ x) = (σ y) ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq97275 eq16177
    | exact resolve eq16177 eq97275
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq16177 eq97275
  have eq97485 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq97328
  have eq97568 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ (M.op x y)) = (σ y) ∨ x = y ∨ (σ x) = (σ y) := by
    first
    | exact superpose eq27 eq97485
    | exact resolve eq97485 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97485
  have eq97590 : (σ x) = (σ y) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | (have r₁ := eq97568
       have r₂ := eq28
       grind)
    | exact resolve eq97568 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97568
  have eq97598 : y = (τ (σ x)) ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq97590 eq30
    | exact resolve eq30 eq97590
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97590
  have eq97726 : x = y ∨ x = y ∨ (σ (M.op x y)) = (σ y) := by
    first
    | exact superpose eq29 eq97598
    | exact resolve eq97598 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97598
  have eq97727 : (σ (M.op x y)) = (σ y) ∨ x = y := by grind
  clear eq97726
  have eq97748 : y = (τ (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq97727 eq30
    | exact resolve eq30 eq97727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq97764 : (M.op y y) = (τ (M.op (σ (M.op x y)) (σ (M.op x y)))) ∨ x = y := by
    first
    | exact superpose eq97727 eq131
    | exact resolve eq131 eq97727
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq131 eq97727
  have eq98108 : (M.op y y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq164 eq97764
    | exact resolve eq97764 eq164
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97764
  have eq98122 : y = (M.op x y) ∨ x = y := by
    first
    | exact superpose eq31 eq97748
    | exact resolve eq97748 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97748
  have eq98143 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) X0) ∨ x = y := by
    intro X0
    first
    | exact superpose eq98122 eq53
    | exact resolve eq53 eq98122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq98158 : (σ (M.op y y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | exact superpose eq98122 eq125
    | exact resolve eq125 eq98122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq125
  have eq98597 : (M.op (σ y) (σ y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by
    first
    | (have i₁ := eq98158
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq98158
    | exact resolve eq98158 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98158
  have eq98611 : ∀ X0 : G, (M.op x X0) = (M.op (M.op x y) X0) ∨ x = y := by
    intro X0
    first
    | (have i₁ := eq98143 X0
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq98143
    | (have j0 := eq98143 X0
       grind)
    | exact resolve eq98143 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98143
  have eq99973 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ x = y ∨ x = y := by
    intro X0
    first
    | exact superpose eq98122 eq98611
    | exact resolve eq98611 eq98122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq100014 : (M.op x (M.op x y)) = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq98611 eq98108
    | exact resolve eq98108 eq98611
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98108 eq98611
  have eq100055 : (M.op x (M.op x y)) = (M.op y y) ∨ x = y := by grind
  clear eq100014
  have eq100081 : ∀ X0 : G, (M.op x X0) = (M.op y X0) ∨ x = y := by
    intro X0
    first
    | (have j0 := eq99973 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99973
  have eq101905 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq97
       have i₂ := eq100081 y
       grind)
    | exact superpose eq100081 eq97
    | exact resolve eq97 eq100081
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100081
  have eq102165 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq101905
       have i₂ := eq19
       grind)
    | exact superpose eq19 eq101905
    | exact resolve eq101905 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq101905
  have eq102184 : (σ (M.op x y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | exact superpose eq21 eq102165
    | exact resolve eq102165 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102165
  have eq102279 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq102184 eq98597
    | exact resolve eq98597 eq102184
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98597
  have eq102298 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) ∨ x = y := by grind
  clear eq102279
  have eq102372 : (τ (σ (M.op x y))) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq102298 eq164
    | exact resolve eq164 eq102298
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq164 eq102298
  have eq102431 : (M.op x y) = (M.op (M.op x y) (M.op x y)) ∨ x = y := by
    first
    | exact superpose eq31 eq102372
    | exact resolve eq102372 eq31
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq31 eq102372
  have eq103216 : y = (M.op y y) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq98122 eq102431
    | exact resolve eq102431 eq98122
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98122 eq102431
  have eq103296 : y = (M.op y y) ∨ x = y := by grind
  clear eq103216
  have eq103336 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq97
       have i₂ := eq103296
       grind)
    | exact superpose eq103296 eq97
    | exact resolve eq97 eq103296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq103425 : y = (M.op x (M.op x y)) ∨ x = y ∨ x = y := by
    first
    | (have i₁ := eq100055
       have i₂ := eq103296
       grind)
    | exact superpose eq103296 eq100055
    | exact resolve eq100055 eq103296
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100055 eq103296
  have eq103445 : y = (M.op x (M.op x y)) ∨ x = y := by grind
  clear eq103425
  have eq103551 : (σ y) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq103336
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq103336
    | exact resolve eq103336 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103336
  have eq103574 : y = (k y x) ∨ x = y ∨ x = y := by
    first
    | exact superpose eq103445 eq3685
    | exact resolve eq3685 eq103445
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3685 eq103445
  have eq103585 : y = (k y x) ∨ x = y := by grind
  clear eq103574
  have eq104595 : (σ y) ≠ (σ (M.op y y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq742 x y
       have i₂ := eq103585
       grind)
    | exact superpose eq103585 eq742
    | (have j0 := eq742 x y
       grind)
    | exact resolve eq742 eq103585
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq742 eq103585
  have eq104625 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq104595
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq104595
    | exact resolve eq104595 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104595
  have eq104643 : (σ y) ≠ (M.op (σ y) (σ y)) ∨ (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq104625
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq104625
    | exact resolve eq104625 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104625
  have eq104649 : (M.op (σ x) (σ y)) = (σ (M.op y y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq104643
       have r₂ := eq103551
       grind)
    | exact resolve eq104643 eq103551
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq103551 eq104643
  have eq104653 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq104649
       have i₂ := eq97
       grind)
    | exact superpose eq97 eq104649
    | exact resolve eq104649 eq97
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97 eq104649
  have eq104657 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq104653
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq104653
    | exact resolve eq104653 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104653
  have eq104661 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq104657
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq104657
    | exact resolve eq104657 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104657
  have eq104665 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq27 eq104661
    | exact resolve eq104661 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104661
  have eq104669 : (σ x) = (σ y) ∨ (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ x = y := by
    first
    | (have i₁ := eq104665
       have i₂ := eq25
       grind)
    | exact superpose eq25 eq104665
    | exact resolve eq104665 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104665
  have eq104673 : (M.op (σ x) (σ y)) = (M.op (σ y) (σ y)) ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | (have i₁ := eq104669
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq104669
    | exact resolve eq104669 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq104669
  have eq112202 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) ∨ x = y := by
    first
    | exact superpose eq104673 eq102184
    | exact resolve eq102184 eq104673
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq102184 eq104673
  have eq112223 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ x = y ∨ (σ x) = (σ y) := by grind
  clear eq112202
  have eq112295 : (σ x) = (σ y) ∨ x = y := by
    first
    | (have r₁ := eq112223
       have r₂ := eq28
       grind)
    | exact resolve eq112223 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq112223
  have eq112903 : y = (τ (σ x)) ∨ x = y := by
    first
    | exact superpose eq112295 eq30
    | exact resolve eq30 eq112295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq30 eq112295
  have eq113067 : x = y ∨ x = y := by
    first
    | exact superpose eq29 eq112903
    | exact resolve eq112903 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq112903
  have eq113068 : x = y := by grind
  clear eq113067
  have eq113087 : (M.op x y) = (M.op x x) := by
    first
    | (have i₁ := eq19
       have i₂ := eq113068
       grind)
    | exact superpose eq113068 eq19
    | exact resolve eq19 eq113068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19
  have eq113088 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq25
       have i₂ := eq113068
       grind)
    | exact superpose eq113068 eq25
    | exact resolve eq25 eq113068
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq113068
  have eq113346 : (σ x) = (σ y) := by
    first
    | (have i₁ := eq113088
       have i₂ := eq23
       grind)
    | exact superpose eq23 eq113088
    | exact resolve eq113088 eq23
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq113088
  have eq113376 : (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | exact superpose eq113346 eq27
    | exact resolve eq27 eq113346
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq113346
  have eq113622 : (M.op x x) = (τ (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq113376 eq72
    | exact resolve eq72 eq113376
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq72 eq113376
  have eq113653 : (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    first
    | (have i₁ := eq113622
       have i₂ := eq113087
       grind)
    | exact superpose eq113087 eq113622
    | exact resolve eq113622 eq113087
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113087 eq113622
  have eq113668 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq113653 eq15
    | exact resolve eq15 eq113653
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq113653
  have eq113941 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq21 eq113668
    | exact resolve eq113668 eq21
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21 eq113668
  have eq114030 : False := by grind
  exact eq114030

/-- `Equation3929`: `x ◇ y = (x ◇ (y ◇ y)) ◇ z`.  Vampire refutation replayed step by step.

`x □ y = if m(Y,X) = X then Y else if m(Y,Y) = Y then X else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pyx_x_pyy_y_y_x_pyx_Equation3929 :
    AutBox.GuardAut2 ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0)) Law3929 := by
  classical
  refine AutBox.guardAut2_of ((Lf 1) ⋆ (Lf 0)) (Lf 0) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 1) (Lf 0) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3929.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op b a ≠ a ∨ k a b = b :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op b a = a ∨ M.op b b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op b a = a ∨ M.op b b = b ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op b a) (a)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  have eq10 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq11 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X1 X0) = X0 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X0) ≠ X0 ∨ (k X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq15 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq16 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X1 X1)) X2) := by
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
  have eq28 : (M.op x y) = (τ (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq15
    | (have j0 := eq15 (M.op x y)
       grind)
    | exact resolve eq15 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
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
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq10
    | exact resolve eq10 eq14
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
  have eq41 : ∀ X0 : G, (σ (k X0 (M.op x y))) = (k (σ X0) (σ (M.op x y))) := by
    intro X0
    first
    | exact superpose eq20 eq10
    | (have j0 := eq10 X0 (M.op x y)
       grind)
    | exact resolve eq10 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 : G, (k y X0) = (τ (k (σ y) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq15 (k y X0)
       have i₂ := eq36 X0
       grind)
    | exact superpose eq36 eq15
    | exact resolve eq15 eq36
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq50 : ∀ X0 : G, (k (M.op x y) X0) = (τ (k (σ (M.op x y)) (σ X0))) := by
    intro X0
    first
    | exact superpose eq37 eq15
    | exact resolve eq15 eq37
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq107 : ∀ X0 : G, (k y (τ X0)) = (τ (k (σ y) X0)) := by
    intro X0
    first
    | (have i₁ := eq47 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq47
    | exact resolve eq47 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq124 : ∀ X0 : G, (k (M.op x y) (τ X0)) = (τ (k (σ (M.op x y)) X0)) := by
    intro X0
    first
    | (have i₁ := eq50 (τ X0)
       have i₂ := eq14 X0
       grind)
    | exact superpose eq14 eq50
    | exact resolve eq50 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq50
  have eq174 : y ≠ (M.op x y) ∨ x = (k y x) := by
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
  have eq175 : (σ y) ≠ (M.op (σ x) (σ y)) ∨ (σ x) = (k (σ y) (σ x)) := by
    first
    | exact superpose eq26 eq13
    | (have j0 := eq13 (σ y) (σ x)
       grind)
    | exact resolve eq13 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq177 : ∀ X0 X1 X2 X3 : G, (M.op (M.op X0 (M.op X1 X1)) X2) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq16 (M.op X0 (M.op X1 X1)) X2 X3
       have i₂ := eq16 X0 X1 (M.op X2 X2)
       grind)
    | exact superpose eq16 eq16
    | exact resolve eq16 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq178 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ X2 ∨ (M.op X0 (M.op X1 X1)) = (k X2 (M.op X0 (M.op X1 X1))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 (M.op X1 X1))
       have i₂ := eq16 X0 X1 X2
       grind)
    | exact superpose eq16 eq13
    | (have j0 := eq13 X2 (M.op X0 (M.op X1 X1))
       grind)
    | (have r₁ := eq13 (M.op X0 X1) (M.op X0 (M.op X1 X1))
       have r₂ := eq16 X0 X1 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq179 : ∀ X0 X1 X3 : G, (M.op X0 X1) = (M.op (M.op X0 X1) X3) := by
    intro X0 X1 X3
    first
    | (have i₁ := eq177 X0 X1 x X3
       have i₂ := eq16 X0 X1 x
       grind)
    | exact superpose eq16 eq177
    | exact resolve eq177 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq177
  have eq180 : ∀ X0 : G, (M.op x y) = (M.op (M.op x y) X0) := by
    intro X0
    first
    | (have i₁ := eq179 x y X0
       have i₂ := eq18
       grind)
    | exact superpose eq18 eq179
    | (have j0 := eq179 x y X0
       grind)
    | exact resolve eq179 eq18
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq181 : ∀ X0 : G, (M.op (σ x) (σ y)) = (M.op (M.op (σ x) (σ y)) X0) := by
    intro X0
    first
    | exact superpose eq26 eq179
    | (have j0 := eq179 (σ x) (σ y) X0
       grind)
    | exact resolve eq179 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq185 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op X0 (M.op X1 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq16 X0 X1 x
       have i₂ := eq179 X0 (M.op X1 X1) x
       grind)
    | exact superpose eq179 eq16
    | exact resolve eq16 eq179
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq191 : ∀ X0 : G, (M.op x y) ≠ X0 ∨ (M.op x y) = (k X0 (M.op x y)) := by
    intro X0
    first
    | exact superpose eq180 eq13
    | (have j0 := eq13 X0 (M.op x y)
       grind)
    | (have r₁ := eq13 (M.op x y) (M.op x y)
       have r₂ := eq180 (M.op x y)
       grind)
    | exact resolve eq13 eq180
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq180
  have eq200 : (M.op x y) = (k (M.op x y) (M.op x y)) := by
    first
    | (have j0 := eq191 (M.op x y)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq191
  have eq202 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq200 eq41
    | exact resolve eq41 eq200
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq41 eq200
  have eq203 : (σ (M.op x y)) = (k (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq20 eq202
    | exact resolve eq202 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq202
  have eq794 : ∀ X0 : G, (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op (M.op (σ x) (σ y)) X0) = X0 ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | exact superpose eq181 eq12
    | (have j0 := eq12 X0 (M.op (σ x) (σ y))
       grind)
    | (have r₁ := eq12 X0 (M.op (σ x) (σ y))
       have r₂ := eq181 (M.op (σ x) (σ y))
       grind)
    | exact resolve eq12 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq795 : ∀ X0 : G, (M.op (M.op (σ x) (σ y)) X0) = X0 ∨ (k X0 (M.op (σ x) (σ y))) = X0 := by
    intro X0
    first
    | (have j0 := eq794 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq794
  have eq798 : ∀ X0 : G, (k X0 (M.op (σ x) (σ y))) = X0 ∨ (M.op (σ x) (σ y)) = X0 := by
    intro X0
    first
    | exact superpose eq181 eq795
    | (have j0 := eq795 X0
       grind)
    | exact resolve eq795 eq181
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq181 eq795
  have eq809 : (M.op x y) = (k y x) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
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
  have eq811 : (M.op (σ x) (σ y)) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq26 eq11
    | (have j0 := eq11 (σ y) (σ x)
       grind)
    | exact resolve eq11 eq26
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq814 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X1 ∨ (M.op X1 X0) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq13 X0 X1
       have i₂ := eq11 X0 X1
       grind)
    | exact superpose eq11 eq13
    | (have j0 := eq13 X0 X1
       have j1 := eq11 X1 X1
       grind)
    | (have r₁ := eq13 X1 X1
       have r₂ := eq11 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq11 X0 X1
       grind)
    | exact resolve eq13 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq826 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq827 : ∀ X0 X1 : G, (k X1 X0) ≠ X1 ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq11 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq828 : ∀ X0 : G, (k X0 X0) ≠ X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq826 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq826
  have eq839 : ∀ X0 X1 : G, (k X0 X1) ≠ X0 ∨ (k X0 X1) = X1 ∨ (M.op X1 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq814 X0 X1
       have j1 := eq13 X0 X1
       grind)
    | (have r₁ := eq814 X1 X1
       have r₂ := eq13 X1 X1
       grind)
    | (have r₁ := eq814 X0 X0
       have r₂ := eq13 X0 X0
       grind)
    | (have r₁ := eq814 X0 X1
       have r₂ := eq13 X0 X1
       grind)
    | exact resolve eq814 eq13
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq814
  have eq847 : (τ (σ (M.op x y))) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) ∨ (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq798 eq124
    | (have j1 := eq798 (σ (M.op x y))
       grind)
    | exact resolve eq124 eq798
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124 eq798
  have eq852 : (τ (σ (M.op x y))) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) := by
    first
    | (have r₁ := eq847
       have r₂ := eq27
       grind)
    | exact resolve eq847 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq847
  have eq858 : (M.op x y) = (k (M.op x y) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq28 eq852
    | exact resolve eq852 eq28
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq28 eq852
  have eq860 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq858 eq38
    | exact resolve eq38 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq38
  have eq861 : (σ (M.op x y)) = (k (σ (M.op x y)) (M.op (σ x) (σ y))) := by
    first
    | exact superpose eq20 eq860
    | exact resolve eq860 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq860
  have eq989 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by
    first
    | exact superpose eq203 eq828
    | (have j0 := eq828 (σ (M.op x y))
       grind)
    | (have r₁ := eq828 (σ (M.op x y))
       have r₂ := eq203
       grind)
    | exact resolve eq828 eq203
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq203 eq828
  have eq992 : (σ (M.op x y)) = (M.op (σ (M.op x y)) (σ (M.op x y))) := by grind
  clear eq989
  have eq996 : ∀ X0 : G, (σ (M.op x y)) = (M.op (σ (M.op x y)) X0) := by
    intro X0
    first
    | exact superpose eq992 eq179
    | exact resolve eq179 eq992
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq992
  have eq1226 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 y
       have i₂ := eq809
       grind)
    | exact superpose eq809 eq39
    | exact resolve eq39 eq809
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq1227 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq1226
       have i₂ := eq24
       grind)
    | exact superpose eq24 eq1226
    | exact resolve eq1226 eq24
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1226
  have eq1229 : (σ (M.op x y)) = (k (σ y) (σ x)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq20 eq1227
    | exact resolve eq1227 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1227
  have eq2037 : (M.op x y) ≠ (M.op x y) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) ∨ (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) := by
    first
    | exact superpose eq858 eq839
    | (have j0 := eq839 x (τ (M.op (σ x) (σ y)))
       grind)
    | (have r₁ := eq839 (M.op x y) (τ (M.op (σ x) (σ y)))
       have r₂ := eq858
       grind)
    | exact resolve eq839 eq858
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq839 eq858
  have eq2091 : (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) (τ (M.op (σ x) (σ y)))) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by grind
  clear eq2037
  have eq2135 : ∀ X0 : G, (τ (M.op (σ x) (σ y))) = (M.op (τ (M.op (σ x) (σ y))) X0) ∨ (M.op x y) = (τ (M.op (σ x) (σ y))) := by
    intro X0
    first
    | exact superpose eq2091 eq179
    | exact resolve eq179 eq2091
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2091
  have eq2589 : ∀ X0 X1 : G, (M.op X0 (M.op X1 X1)) = (k (M.op X0 X1) (M.op X0 (M.op X1 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq178 X0 X1 (M.op X0 X1)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq178
  have eq2590 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq2589 X0 X1
       have i₂ := eq185 X0 X1
       grind)
    | exact superpose eq185 eq2589
    | exact resolve eq2589 eq185
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq185 eq2589
  have eq3412 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | exact superpose eq1229 eq811
    | exact resolve eq811 eq1229
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1229
  have eq3422 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    first
    | (have r₁ := eq3412
       have r₂ := eq27
       grind)
    | exact resolve eq3412 eq27
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3412
  have eq3487 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x x) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3422 eq179
    | exact resolve eq179 eq3422
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3422
  have eq3502 : x = (M.op x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3487 eq26
    | (have j1 := eq3487 (σ y)
       grind)
    | exact resolve eq26 eq3487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3487
  have eq3532 : ∀ X0 : G, x = (M.op x X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have i₁ := eq179 x x x
       have i₂ := eq3502
       grind)
    | exact superpose eq3502 eq179
    | exact resolve eq179 eq3502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq3534 : x = (k x x) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq2590 x x
       have i₂ := eq3502
       grind)
    | exact superpose eq3502 eq2590
    | exact resolve eq2590 eq3502
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2590 eq3502
  have eq3547 : (σ y) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq3532 y
       grind)
    | exact superpose eq3532 eq18
    | (have j1 := eq3532 y
       grind)
    | exact resolve eq18 eq3532
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3532
  have eq3574 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3547 eq175
    | (have r₁ := eq175
       have r₂ := eq3547
       grind)
    | exact resolve eq175 eq3547
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3547
  have eq3661 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3574
  have eq3774 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq39 x
       have i₂ := eq3534
       grind)
    | exact superpose eq3534 eq39
    | exact resolve eq39 eq3534
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39 eq3534
  have eq3780 : (σ x) = (k (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq3774
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq3774
    | exact resolve eq3774 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3774
  have eq3866 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3780 eq827
    | (have j0 := eq827 (σ x) (σ x)
       grind)
    | (have r₁ := eq827 (σ x) (σ x)
       have r₂ := eq3780
       grind)
    | exact resolve eq827 eq3780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq827 eq3780
  have eq3867 : (σ x) ≠ (σ x) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3866
  have eq3868 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq3867
  have eq3928 : (τ (σ x)) = (k y (τ (σ x))) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq3661 eq107
    | exact resolve eq107 eq3661
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3661
  have eq3936 : x = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq3928
    | exact resolve eq3928 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3928
  have eq3939 : x = (k y x) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq3936
       have r₂ := eq174
       grind)
    | exact resolve eq3936 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3936
  have eq3943 : x = (M.op x y) ∨ x = (M.op x x) ∨ y = (M.op x y) ∨ x = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq809
       have i₂ := eq3939
       grind)
    | exact superpose eq3939 eq809
    | exact resolve eq809 eq3939
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq809 eq3939
  have eq3947 : x = (M.op x x) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq3943
  have eq4019 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    intro X0
    first
    | exact superpose eq3868 eq179
    | exact resolve eq179 eq3868
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq3868
  have eq4054 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4019 eq26
    | (have j1 := eq4019 (σ y)
       grind)
    | exact resolve eq26 eq4019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4019
  have eq4070 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4054
  have eq4079 : (σ y) ≠ (σ y) ∨ (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4070 eq175
    | (have r₁ := eq175
       have r₂ := eq4070
       grind)
    | exact resolve eq175 eq4070
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq175 eq4070
  have eq4155 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by grind
  clear eq4079
  have eq4455 : (τ (σ x)) = (k y (τ (σ x))) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq4155 eq107
    | exact resolve eq107 eq4155
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq107 eq4155
  have eq4463 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) := by
    first
    | exact superpose eq29 eq4455
    | exact resolve eq4455 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4455
  have eq4466 : x = (k y x) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have r₁ := eq4463
       have r₂ := eq174
       grind)
    | exact resolve eq4463 eq174
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4463
  have eq4471 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq36 x
       have i₂ := eq4466
       grind)
    | exact superpose eq4466 eq36
    | exact resolve eq36 eq4466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq36 eq4466
  have eq4476 : (σ x) = (k (σ y) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq4471
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq4471
    | exact resolve eq4471 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4471
  have eq4482 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ x)) ∨ (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4476 eq811
    | exact resolve eq811 eq4476
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq811 eq4476
  have eq4487 : (σ x) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by grind
  clear eq4482
  have eq4580 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | exact superpose eq4487 eq179
    | exact resolve eq179 eq4487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4487
  have eq4594 : (σ x) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ (σ y) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4580 eq26
    | (have j1 := eq4580 (σ y)
       grind)
    | exact resolve eq26 eq4580
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4580
  have eq4610 : (σ y) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ x) (σ y)) := by grind
  clear eq4594
  have eq4618 : (σ (M.op x y)) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq4610 eq27
    | exact resolve eq27 eq4610
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4610
  have eq5645 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    intro X0
    first
    | (have i₁ := eq179 x x x
       have i₂ := eq3947
       grind)
    | exact superpose eq3947 eq179
    | exact resolve eq179 eq3947
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq179 eq3947
  have eq5733 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) ∨ (σ x) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5645 y
       grind)
    | exact superpose eq5645 eq18
    | (have j1 := eq5645 y
       grind)
    | exact resolve eq18 eq5645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5645
  have eq5749 : (σ x) = (M.op (σ x) (σ y)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq5733
  have eq5790 : ∀ X0 : G, (τ (σ x)) = (M.op (τ (σ x)) X0) ∨ (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq5749 eq2135
    | exact resolve eq2135 eq5749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2135 eq5749
  have eq5890 : ∀ X0 : G, x = (M.op x X0) ∨ (M.op x y) = (τ (σ x)) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq5790
    | exact resolve eq5790 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5790
  have eq5929 : ∀ X0 : G, x = (M.op x y) ∨ x = (M.op x X0) ∨ y = (M.op x y) ∨ x = (M.op x y) := by
    intro X0
    first
    | exact superpose eq29 eq5890
    | (have j0 := eq5890 y
       grind)
    | exact resolve eq5890 eq29
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq29 eq5890
  have eq5930 : ∀ X0 : G, x = (M.op x X0) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    intro X0
    first
    | (have j0 := eq5929 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5929
  have eq6143 : x = (M.op x y) ∨ x = (M.op x y) ∨ y = (M.op x y) := by
    first
    | (have i₁ := eq18
       have i₂ := eq5930 y
       grind)
    | exact superpose eq5930 eq18
    | (have j1 := eq5930 y
       grind)
    | exact resolve eq18 eq5930
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18 eq5930
  have eq6159 : y = (M.op x y) ∨ x = (M.op x y) := by grind
  clear eq6143
  have eq6168 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq24
       have i₂ := eq6159
       grind)
    | exact superpose eq6159 eq24
    | exact resolve eq24 eq6159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24
  have eq6171 : (M.op x y) ≠ (M.op x y) ∨ x = (k (M.op x y) x) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq174
       have i₂ := eq6159
       grind)
    | exact superpose eq6159 eq174
    | (have r₁ := eq174
       have r₂ := eq6159
       grind)
    | exact resolve eq174 eq6159
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq174 eq6159
  have eq6204 : x = (k (M.op x y) x) ∨ x = (M.op x y) := by grind
  clear eq6171
  have eq6212 : (σ (M.op x y)) = (σ y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq20 eq6168
    | exact resolve eq6168 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6168
  have eq6235 : (σ y) = (k (σ y) (M.op (σ x) (σ y))) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6212 eq861
    | exact resolve eq861 eq6212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq861
  have eq6266 : (σ y) ≠ (σ y) ∨ (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6212 eq4618
    | (have r₁ := eq4618
       have r₂ := eq6212
       grind)
    | exact resolve eq4618 eq6212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4618
  have eq6274 : (σ x) = (M.op (σ x) (σ y)) ∨ x = (M.op x y) := by grind
  clear eq6266
  have eq6287 : (σ y) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6274 eq6235
    | exact resolve eq6235 eq6274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6235
  have eq6312 : (σ (M.op x y)) ≠ (σ x) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6274 eq27
    | exact resolve eq27 eq6274
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6274
  have eq6486 : (σ x) ≠ (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6212 eq6312
    | exact resolve eq6312 eq6212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6312
  have eq6487 : (σ x) ≠ (σ y) ∨ x = (M.op x y) := by grind
  clear eq6486
  have eq6514 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6204 eq37
    | exact resolve eq37 eq6204
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq37 eq6204
  have eq6520 : (σ x) = (k (σ (M.op x y)) (σ x)) ∨ x = (M.op x y) := by
    first
    | (have i₁ := eq6514
       have i₂ := eq22
       grind)
    | exact superpose eq22 eq6514
    | exact resolve eq6514 eq22
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6514
  have eq6522 : (σ x) = (k (σ y) (σ x)) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6212 eq6520
    | exact resolve eq6520 eq6212
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6212 eq6520
  have eq6624 : (σ x) = (σ y) ∨ x = (M.op x y) ∨ x = (M.op x y) := by
    first
    | exact superpose eq6522 eq6287
    | exact resolve eq6287 eq6522
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6287 eq6522
  have eq6628 : (σ x) = (σ y) ∨ x = (M.op x y) := by grind
  clear eq6624
  have eq6632 : x = (M.op x y) := by
    first
    | (have r₁ := eq6628
       have r₂ := eq6487
       grind)
    | exact resolve eq6628 eq6487
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6487 eq6628
  have eq6638 : (σ (M.op x y)) = (σ x) := by
    first
    | (have i₁ := eq22
       have i₂ := eq6632
       grind)
    | exact superpose eq6632 eq22
    | exact resolve eq22 eq6632
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq22 eq6632
  have eq6660 : (σ (M.op x y)) = (σ x) := by
    first
    | exact superpose eq6638 eq20
    | exact resolve eq20 eq6638
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq6638
  have eq6816 : ∀ X0 : G, (σ x) = (M.op (σ x) X0) := by
    intro X0
    first
    | exact superpose eq6660 eq996
    | exact resolve eq996 eq6660
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq996
  have eq6920 : (σ x) = (M.op (σ x) (σ y)) := by
    first
    | exact superpose eq6816 eq26
    | (have j1 := eq6816 (σ y)
       grind)
    | exact resolve eq26 eq6816
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26 eq6816
  have eq6946 : (σ (M.op x y)) ≠ (σ x) := by
    first
    | exact superpose eq6920 eq27
    | exact resolve eq27 eq6920
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27 eq6920
  have eq7046 : False := by grind
  exact eq7046

/-- `Equation3930`: `x ◇ y = (x ◇ (y ◇ z)) ◇ x`.  Vampire refutation replayed step by step.

`x □ y = if m(X,Y) = Y then X else if m(Y,Y) = Y then m(X,Y) else m(Y,Y)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxy_y_pyy_y_x_pxy_pyy_Equation3930 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1)) Law3930 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 1)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 1) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 1))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3930.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a b ≠ b ∨ k a b = a :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a b = b ∨ M.op b b ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a b = b ∨ M.op b b = b ∨ k a b = M.op b b :=
    fun a b ↦ (eq_or_ne (M.op a b) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (b)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X0 (M.op X1 X2)) X0) := by
    intro X0 X1 X2
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X1 ∨ (k X0 X1) = X0 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X1 X1) ≠ X1 ∨ (M.op X0 X1) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (M.op X1 X1) = X1 ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    grind
  have eq15 : ∀ X0 X1 : G, (σ (k X0 X1)) = (k (σ X0) (σ X1)) := by
    intro X0 X1
    grind
  have eq16 : (σ (M.op x y)) ≠ (M.op (σ x) (σ y)) := by grind
  clear hm ht hu hv hd nh hM hi1 hi2
  have eq17 : ∀ X0 X1 : G, (k X0 X1) = (τ (k (σ X0) (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (k X0 X1)
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq10
    | exact resolve eq10 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq17 (τ X0) X1
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq17
    | exact resolve eq17 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq23 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq18
    | exact resolve eq18 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18
  have eq44 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 X3))) = (M.op (M.op X2 (M.op X0 X1)) X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq9 X2 (M.op X0 (M.op X1 X3)) X0
       have i₂ := eq9 X0 X1 X3
       grind)
    | exact superpose eq9 eq9
    | exact resolve eq9 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq47 : ∀ X0 X1 X2 X3 : G, (M.op X2 (M.op X0 (M.op X1 X3))) = (M.op X2 X0) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq44 X0 X1 X2 X3
       have i₂ := eq9 X2 X0 X1
       grind)
    | exact superpose eq9 eq44
    | exact resolve eq44 eq9
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq44
  have eq51 : ∀ X0 X2 X4 : G, (M.op X4 (M.op X2 X0)) = (M.op X4 X2) := by
    intro X0 X2 X4
    first
    | (have i₁ := eq47 X2 X0 X4 (M.op x x)
       have i₂ := eq47 X0 x X2 x
       grind)
    | exact superpose eq47 eq47
    | exact resolve eq47 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq53 : ∀ X0 X2 : G, (M.op X2 X0) = (M.op (M.op X2 X0) X2) := by
    intro X0 X2
    first
    | (have i₁ := eq9 X2 X0 (M.op x x)
       have i₂ := eq47 X0 x X2 x
       grind)
    | exact superpose eq47 eq9
    | exact resolve eq9 eq47
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq47
  have eq62 : ∀ X0 X1 X2 : G, (k X2 (M.op X0 X1)) = X2 ∨ (M.op X0 X1) ≠ (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq12 X2 (M.op X0 X1)
       have i₂ := eq51 X1 X0 X2
       grind)
    | exact superpose eq51 eq12
    | (have j0 := eq12 X2 (M.op X0 X1)
       grind)
    | (have r₁ := eq12 x (M.op x x)
       have r₂ := eq51 x x x
       grind)
    | exact resolve eq12 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq68 : ∀ X0 X1 : G, (M.op X0 X1) ≠ X0 ∨ (M.op X0 X1) = (k (M.op X0 X1) X0) := by
    intro X0 X1
    first
    | (have i₁ := eq12 (M.op X0 X1) X0
       have i₂ := eq53 X1 X0
       grind)
    | exact superpose eq53 eq12
    | (have j0 := eq12 (M.op X0 X1) X0
       grind)
    | exact resolve eq12 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq86 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X2) ∨ (σ X0) = (k (σ X0) (σ (M.op X1 X2))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 (M.op X1 X2)
       have i₂ := eq62 X1 X2 X0
       grind)
    | exact superpose eq62 eq15
    | (have j1 := eq62 X1 X2 X0
       grind)
    | exact resolve eq15 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq87 : ∀ X0 X1 : G, (M.op X0 X1) ≠ (M.op X0 X1) ∨ (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have i₁ := eq68 (M.op x X0) x
       have i₂ := eq53 X0 x
       grind)
    | exact superpose eq53 eq68
    | (have r₁ := eq68 (M.op x X0) x
       have r₂ := eq53 X0 x
       grind)
    | exact resolve eq68 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq91 : ∀ X0 X1 : G, (M.op X0 X1) = (k (M.op X0 X1) (M.op X0 X1)) := by
    intro X0 X1
    first
    | (have j0 := eq87 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq87
  have eq95 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (k (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq23 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq23
    | exact resolve eq23 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq96 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (k (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq15 (M.op X0 X1) (M.op X0 X1)
       have i₂ := eq91 X0 X1
       grind)
    | exact superpose eq91 eq15
    | exact resolve eq15 eq91
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq91
  have eq97 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X0 X1) = (M.op X2 (M.op X0 X1)) ∨ (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 (M.op X0 X1)
       have i₂ := eq51 X1 X0 (M.op X0 X1)
       grind)
    | exact superpose eq51 eq13
    | (have j0 := eq13 X2 (M.op X0 X1)
       grind)
    | exact resolve eq13 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq98 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 (M.op X0 X1)) ∨ (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq97 X0 X1 X2
       grind)
    | (have r₁ := eq97 X2 X0 X2
       have r₂ := eq53 X0 X2
       grind)
    | exact resolve eq97 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq97
  have eq99 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X2 X0) ∨ (M.op X2 (M.op X0 X1)) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq98 X0 X1 X2
       have i₂ := eq51 X1 X0 X2
       grind)
    | exact superpose eq51 eq98
    | (have j0 := eq98 X0 X1 X2
       grind)
    | exact resolve eq98 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq98
  have eq100 : ∀ X0 X1 X2 : G, (M.op X2 X0) = (k X2 (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X2 X0) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq99 X0 X1 X2
       have i₂ := eq51 X1 X0 X2
       grind)
    | exact superpose eq51 eq99
    | (have j0 := eq99 X0 X1 X2
       grind)
    | exact resolve eq99 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq99
  have eq124 : ∀ X0 X1 X2 : G, (k (σ X0) (σ (M.op X1 X2))) = (σ (M.op X0 X1)) ∨ (M.op X0 X1) = (M.op X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq15 X0 (M.op X1 X2)
       have i₂ := eq100 X1 X2 X0
       grind)
    | exact superpose eq100 eq15
    | (have j1 := eq100 X1 X2 X0
       grind)
    | exact resolve eq15 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq135 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) ∨ (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (σ (M.op X0 X1)) (σ (M.op X0 X1))
       have i₂ := eq96 X0 X1
       grind)
    | exact superpose eq96 eq14
    | (have j0 := eq14 (σ (M.op X0 X1)) (σ (M.op X0 X1))
       grind)
    | exact resolve eq14 eq96
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq96
  have eq136 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) ∨ (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have i₁ := eq14 (τ (M.op X0 X1)) (τ (M.op X0 X1))
       have i₂ := eq95 X0 X1
       grind)
    | exact superpose eq95 eq14
    | (have j0 := eq14 (τ (M.op X0 X1)) (τ (M.op X0 X1))
       grind)
    | exact resolve eq14 eq95
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq95
  have eq138 : ∀ X0 X1 : G, (M.op X1 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq15 X0 X1
       have i₂ := eq14 X0 X1
       grind)
    | exact superpose eq14 eq15
    | (have j1 := eq14 X1 X1
       grind)
    | exact resolve eq15 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq141 : ∀ X0 X1 : G, (τ (M.op X0 X1)) = (M.op (τ (M.op X0 X1)) (τ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq136 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq136
  have eq142 : ∀ X0 X1 : G, (σ (M.op X0 X1)) = (M.op (σ (M.op X0 X1)) (σ (M.op X0 X1))) := by
    intro X0 X1
    first
    | (have j0 := eq135 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq135
  have eq476 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) ≠ (M.op X2 (τ (M.op X0 X1))) ∨ (σ X2) = (k (σ X2) (σ (τ (M.op X0 X1)))) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq86 X0 (τ (M.op X0 X1)) (τ (M.op X0 X1))
       have i₂ := eq141 X0 X1
       grind)
    | exact superpose eq141 eq86
    | exact resolve eq86 eq141
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq86 eq141
  have eq478 : ∀ X0 X1 X2 : G, (τ (M.op X0 X1)) ≠ (M.op X2 (τ (M.op X0 X1))) ∨ (σ X2) = (k (σ X2) (M.op X0 X1)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq476 X0 X1 X2
       have i₂ := eq11 (M.op X0 X1)
       grind)
    | exact superpose eq11 eq476
    | (have j0 := eq476 X0 X1 X2
       grind)
    | exact resolve eq476 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq476
  have eq497 : ∀ X0 X1 X2 : G, X1 ≠ X1 ∨ (M.op X2 X1) = X1 ∨ (M.op X2 X1) = (k X2 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq13 X2 X1
       have i₂ := eq138 X0 X1
       grind)
    | exact superpose eq138 eq13
    | (have j0 := eq13 X2 X1
       have j1 := eq138 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq138 X0 X1
       grind)
    | (have r₁ := eq13 X0 X1
       have r₂ := eq138 X1 X1
       grind)
    | exact resolve eq13 eq138
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq517 : ∀ X0 : G, X0 ≠ X0 ∨ (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq138 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq138
  have eq518 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have j0 := eq517 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq517
  have eq519 : ∀ X0 X1 X2 : G, (M.op X2 X1) = X1 ∨ (M.op X2 X1) = (k X2 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1 X2
    first
    | (have j0 := eq497 X0 X1 X2
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq497
  have eq560 : ∀ X0 : G, (M.op X0 X0) = (τ (k (σ X0) (σ X0))) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq10 (M.op X0 X0)
       have i₂ := eq518 X0
       grind)
    | exact superpose eq518 eq10
    | (have j1 := eq518 X0
       grind)
    | exact resolve eq10 eq518
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq518
  have eq568 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq560 X0
       have i₂ := eq17 X0 X0
       grind)
    | exact superpose eq17 eq560
    | (have j0 := eq560 X0
       grind)
    | exact resolve eq560 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq560
  have eq1670 : ∀ X0 X1 : G, X1 ≠ X1 ∨ (M.op X0 X1) = (k X0 X1) ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op X0 X1) = X1 := by
    intro X0 X1
    first
    | (have j0 := eq519 X0 X1 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq519
  have eq1671 : ∀ X0 X1 : G, (M.op X0 X1) = X1 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq1670 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1670
  have eq2491 : ∀ X0 X1 : G, X1 ≠ X1 ∨ (k X0 X1) = X0 ∨ (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq12 X0 X1
       have i₂ := eq1671 X0 X1
       grind)
    | exact superpose eq1671 eq12
    | (have j0 := eq12 X0 X1
       have j1 := eq1671 X0 X1
       grind)
    | (have r₁ := eq12 X0 X1
       have r₂ := eq1671 X0 X1
       grind)
    | exact resolve eq12 eq1671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2492 : ∀ X0 X1 X2 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op X2 X0) = (M.op X2 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq51 X1 X0 X2
       have i₂ := eq1671 X0 X1
       grind)
    | exact superpose eq1671 eq51
    | (have j1 := eq1671 X0 X1
       grind)
    | exact resolve eq51 eq1671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq2493 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq53 X1 X0
       have i₂ := eq1671 X0 X1
       grind)
    | exact superpose eq1671 eq53
    | (have j1 := eq1671 X0 X1
       grind)
    | exact resolve eq53 eq1671
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1671
  have eq2560 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X1)) ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq2491 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2491
  have eq7050 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (k (σ X0) (σ X1))) ∨ (M.op X1 X0) = X1 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq2493 X0 X1
       grind)
    | exact superpose eq2493 eq10
    | (have j1 := eq2493 X0 X1
       grind)
    | exact resolve eq10 eq2493
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2493
  have eq7063 : ∀ X0 X1 : G, (M.op X1 X0) = X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq7050 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq7050
    | (have j0 := eq7050 X0 X1
       grind)
    | exact resolve eq7050 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7050
  have eq7149 : ∀ X0 X1 : G, X1 ≠ X1 ∨ (k X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq68 X1 X0
       have i₂ := eq7063 X0 X1
       grind)
    | exact superpose eq7063 eq68
    | (have j1 := eq7063 X0 X1
       grind)
    | (have r₁ := eq68 X1 X0
       have r₂ := eq7063 X0 X1
       grind)
    | exact resolve eq68 eq7063
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq68 eq7063
  have eq7341 : ∀ X0 X1 : G, (k X1 X1) = X1 ∨ (k X0 X1) = (M.op X1 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have j0 := eq7149 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7149
  have eq8176 : ∀ X0 X1 : G, (M.op X1 X1) = (τ (k (σ X0) (σ X1))) ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq10 (M.op X1 X1)
       have i₂ := eq2560 X0 X1
       grind)
    | exact superpose eq2560 eq10
    | (have j1 := eq2560 X0 X1
       grind)
    | exact resolve eq10 eq2560
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2560
  have eq8192 : ∀ X0 X1 : G, (k X0 X1) = (M.op X1 X1) ∨ (k X0 X1) = X0 ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1
    first
    | (have i₁ := eq8176 X0 X1
       have i₂ := eq17 X0 X1
       grind)
    | exact superpose eq17 eq8176
    | (have j0 := eq8176 X0 X1
       grind)
    | exact resolve eq8176 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8176
  have eq14457 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X2) (M.op X1 X2)) ∨ (M.op X0 X1) = (M.op X1 X2) ∨ (k X0 (M.op X1 X2)) = X0 ∨ (M.op X0 (M.op X1 X2)) = (k X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq100 X1 X2 X0
       have i₂ := eq8192 X0 (M.op X1 X2)
       grind)
    | exact superpose eq8192 eq100
    | (have j0 := eq100 X1 X2 X0
       have j1 := eq8192 X0 (M.op X1 X2)
       grind)
    | exact resolve eq100 eq8192
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq8192
  have eq14630 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X2) (M.op X1 X2)) ∨ (k X0 (M.op X1 X2)) = X0 ∨ (M.op X0 (M.op X1 X2)) = (k X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq14457 X0 X1 X2
       have j1 := eq62 X1 X2 X0
       grind)
    | (have r₁ := eq14457 (M.op X1 X2) X1 X2
       have r₂ := eq62 (M.op X1 X2) X1 (M.op X1 X2)
       grind)
    | (have r₁ := eq14457 X0 X2 X0
       have r₂ := eq62 X0 X2 X2
       grind)
    | (have r₁ := eq14457 X2 X0 X1
       have r₂ := eq62 X0 X1 X2
       grind)
    | exact resolve eq14457 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14457
  have eq14655 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op (M.op X1 X2) X1) ∨ (k X0 (M.op X1 X2)) = X0 ∨ (M.op X0 (M.op X1 X2)) = (k X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14630 X0 X1 X2
       have i₂ := eq51 X2 X1 (M.op X1 X2)
       grind)
    | exact superpose eq51 eq14630
    | (have j0 := eq14630 X0 X1 X2
       grind)
    | exact resolve eq14630 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14630
  have eq14663 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (M.op X1 X2) ∨ (k X0 (M.op X1 X2)) = X0 ∨ (M.op X0 (M.op X1 X2)) = (k X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14655 X0 X1 X2
       have i₂ := eq53 X2 X1
       grind)
    | (have i₁ := eq14655 X0 X0 X2
       have i₂ := eq53 X0 (M.op X0 X2)
       grind)
    | exact superpose eq53 eq14655
    | (have j0 := eq14655 X0 X1 X2
       grind)
    | exact resolve eq14655 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14655
  have eq14667 : ∀ X0 X1 X2 : G, (k X0 (M.op X1 X2)) = X0 ∨ (M.op X0 (M.op X1 X2)) = (k X0 (M.op X1 X2)) := by
    intro X0 X1 X2
    first
    | (have j0 := eq14663 X0 X1 X2
       have j1 := eq62 X1 X2 X0
       grind)
    | (have r₁ := eq14663 X0 X2 X0
       have r₂ := eq62 X0 X2 X2
       grind)
    | (have r₁ := eq14663 X2 X0 X1
       have r₂ := eq62 X0 X1 X2
       grind)
    | exact resolve eq14663 eq62
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq62 eq14663
  have eq14668 : ∀ X0 X1 X2 : G, (M.op X0 X1) = (k X0 (M.op X1 X2)) ∨ (k X0 (M.op X1 X2)) = X0 := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14667 X0 X1 X2
       have i₂ := eq51 X2 X1 X0
       grind)
    | exact superpose eq51 eq14667
    | (have j0 := eq14667 X0 X1 X2
       grind)
    | exact resolve eq14667 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14667
  have eq14909 : ∀ X0 X1 X2 : G, (τ (k (σ X1) (σ X2))) = (M.op X2 X2) ∨ (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq10 (M.op X2 X2)
       have i₂ := eq2492 X1 X2 X0
       grind)
    | exact superpose eq2492 eq10
    | (have j1 := eq2492 X1 X2 X0
       grind)
    | exact resolve eq10 eq2492
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq2492
  have eq14930 : ∀ X0 X1 X2 : G, (k X1 X2) = (M.op X2 X2) ∨ (M.op X0 X1) = (M.op X0 X2) ∨ (M.op X1 X2) = (k X1 X2) := by
    intro X0 X1 X2
    first
    | (have i₁ := eq14909 X0 X1 X2
       have i₂ := eq17 X1 X2
       grind)
    | exact superpose eq17 eq14909
    | (have j0 := eq14909 X0 X1 X2
       grind)
    | exact resolve eq14909 eq17
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq17 eq14909
  have eq18519 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq7341 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq7341
  have eq18520 : ∀ X0 : G, (M.op X0 X0) ≠ X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq18519 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18519
  have eq18527 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq18520 X0
       have j1 := eq568 X0
       grind)
    | (have r₁ := eq18520 X0
       have r₂ := eq568 X0
       grind)
    | exact resolve eq18520 eq568
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq568 eq18520
  have eq18601 : ∀ X0 : G, (σ (M.op X0 X0)) = (k (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq18527 X0
       grind)
    | exact superpose eq18527 eq15
    | exact resolve eq15 eq18527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18602 : ∀ X0 : G, (τ (M.op X0 X0)) = (k (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq23 X0 X0
       have i₂ := eq18527 X0
       grind)
    | exact superpose eq18527 eq23
    | exact resolve eq23 eq18527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq18644 : ∀ X0 : G, (τ (M.op X0 X0)) = (M.op (τ X0) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq18602 X0
       have i₂ := eq18527 (τ X0)
       grind)
    | exact superpose eq18527 eq18602
    | exact resolve eq18602 eq18527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18602
  have eq18645 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq18601 X0
       have i₂ := eq18527 (σ X0)
       grind)
    | exact superpose eq18527 eq18601
    | exact resolve eq18601 eq18527
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18527 eq18601
  have eq18694 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) ≠ (M.op X1 (M.op (τ X0) (τ X0))) ∨ (σ X1) = (k (σ X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq478 X0 X0 x
       have i₂ := eq18644 X0
       grind)
    | exact superpose eq18644 eq478
    | (have j0 := eq478 X0 X0 X1
       grind)
    | exact resolve eq478 eq18644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq478
  have eq18800 : ∀ X0 X1 : G, (M.op (τ X0) (τ X0)) ≠ (M.op X1 (τ X0)) ∨ (σ X1) = (k (σ X1) (M.op X0 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq18694 X0 X1
       have i₂ := eq51 (τ X0) (τ X0) X1
       grind)
    | exact superpose eq51 eq18694
    | (have j0 := eq18694 X0 X1
       grind)
    | (have r₁ := eq18694 X0 (τ X0)
       have r₂ := eq51 (τ X0) (τ X0) (τ X0)
       grind)
    | exact resolve eq18694 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18694
  have eq18888 : ∀ X0 X1 : G, (σ (M.op X1 X0)) = (k (σ X1) (M.op (σ X0) (σ X0))) ∨ (M.op X1 X0) = (M.op X0 X0) := by
    intro X0 X1
    first
    | (have i₁ := eq124 X1 X0 X0
       have i₂ := eq18645 X0
       grind)
    | exact superpose eq18645 eq124
    | (have j0 := eq124 X1 X0 X0
       grind)
    | exact resolve eq124 eq18645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq124
  have eq21266 : ∀ X0 X1 : G, (M.op X1 X0) ≠ (M.op X0 X0) ∨ (σ X1) = (k (σ X1) (M.op (σ X0) (σ X0))) := by
    intro X0 X1
    first
    | (have i₁ := eq18800 (σ X0) X1
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq18800
    | (have j0 := eq18800 (σ X0) X1
       grind)
    | exact resolve eq18800 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18800
  have eq23676 : (M.op (σ x) (σ y)) ≠ (k (σ x) (M.op (σ y) (σ y))) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq16
       have i₂ := eq18888 y x
       grind)
    | exact superpose eq18888 eq16
    | (have j1 := eq18888 y x
       grind)
    | exact resolve eq16 eq18888
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18888
  have eq26909 : ∀ X0 X1 X2 : G, (M.op X0 X1) ≠ (M.op X1 X1) ∨ (M.op X2 X0) = (M.op X2 X1) ∨ (M.op X0 X1) = (k X0 X1) := by
    intro X0 X1 X2
    first
    | (have j0 := eq14930 X2 X0 X1
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14930
  have eq27249 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) ≠ (M.op (M.op X0 X1) (M.op X0 X1)) ∨ (M.op X3 X2) = (M.op X3 (M.op X0 X1)) ∨ (M.op X2 X0) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq26909 x (M.op X2 X0) X2
       have i₂ := eq51 X0 X2 x
       grind)
    | exact superpose eq51 eq26909
    | (have j0 := eq26909 X2 (M.op X0 X1) X3
       grind)
    | exact resolve eq26909 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq26909
  have eq27289 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) ≠ (M.op (M.op X0 X1) X0) ∨ (M.op X3 X2) = (M.op X3 (M.op X0 X1)) ∨ (M.op X2 X0) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq27249 X0 X1 X2 X3
       have i₂ := eq51 X1 X0 (M.op X0 X1)
       grind)
    | exact superpose eq51 eq27249
    | (have j0 := eq27249 X0 X1 X2 X3
       grind)
    | (have r₁ := eq27249 X2 X0 (M.op X2 X0) X3
       have r₂ := eq51 X0 X2 (M.op X2 X0)
       grind)
    | exact resolve eq27249 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27249
  have eq27292 : ∀ X0 X1 X2 X3 : G, (M.op X0 X1) ≠ (M.op X2 X0) ∨ (M.op X3 X2) = (M.op X3 (M.op X0 X1)) ∨ (M.op X2 X0) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq27289 X0 X1 X2 X3
       have i₂ := eq53 X1 X0
       grind)
    | (have i₁ := eq27289 X0 X1 X2 X3
       have i₂ := eq53 X0 (M.op X0 X1)
       grind)
    | exact superpose eq53 eq27289
    | (have j0 := eq27289 X0 X1 X2 X3
       grind)
    | (have r₁ := eq27289 X2 X2 X2 X3
       have r₂ := eq53 X2 X2
       grind)
    | exact resolve eq27289 eq53
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27289
  have eq27294 : ∀ X0 X1 X2 X3 : G, (M.op X3 X2) = (M.op X3 (M.op X0 X1)) ∨ (M.op X2 X0) = (k X2 (M.op X0 X1)) := by
    intro X0 X1 X2 X3
    first
    | (have j0 := eq27292 X0 X1 X2 X3
       have j1 := eq100 X0 X1 X2
       grind)
    | (have r₁ := eq27292 X0 X1 X2 X3
       have r₂ := eq100 X0 X1 X2
       grind)
    | (have r₁ := eq27292 X1 X0 X0 X3
       have r₂ := eq100 X0 X1 X1
       grind)
    | exact resolve eq27292 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27292
  have eq27295 : ∀ X0 X1 X2 X3 : G, (M.op X2 X0) = (k X2 (M.op X0 X1)) ∨ (M.op X3 X0) = (M.op X3 X2) := by
    intro X0 X1 X2 X3
    first
    | (have i₁ := eq27294 X0 X1 X2 X3
       have i₂ := eq51 X1 X0 X3
       grind)
    | exact superpose eq51 eq27294
    | (have j0 := eq27294 X0 X1 X2 X3
       grind)
    | exact resolve eq27294 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27294
  have eq33925 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ y)) ∨ (M.op x y) = (M.op y y) ∨ (σ x) = (k (σ x) (M.op (σ y) (σ y))) := by
    first
    | (have i₁ := eq23676
       have i₂ := eq14668 (σ x) (σ y) (σ y)
       grind)
    | exact superpose eq14668 eq23676
    | (have j1 := eq14668 (σ x) (σ y) (σ y)
       grind)
    | (have r₁ := eq23676
       have r₂ := eq14668 (σ x) (σ y) (σ y)
       grind)
    | exact resolve eq23676 eq14668
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq14668 eq23676
  have eq33934 : (M.op x y) = (M.op y y) ∨ (σ x) = (k (σ x) (M.op (σ y) (σ y))) := by grind
  clear eq33925
  have eq33943 : (σ x) = (k (σ x) (M.op (σ y) (σ y))) := by
    first
    | (have j1 := eq21266 y x
       grind)
    | (have r₁ := eq33934
       have r₂ := eq21266 y x
       grind)
    | exact resolve eq33934 eq21266
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq21266 eq33934
  have eq33972 : ∀ X0 : G, (σ x) = (M.op (σ x) (σ y)) ∨ (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq33943
       have i₂ := eq27295 (σ y) (σ y) (σ x) X0
       grind)
    | exact superpose eq27295 eq33943
    | (have j1 := eq27295 (σ y) x (σ x) X0
       grind)
    | exact resolve eq33943 eq27295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq33981 : (τ (σ x)) = (k (τ (σ x)) (τ (M.op (σ y) (σ y)))) := by
    first
    | (have i₁ := eq23 (M.op (σ y) (σ y)) (σ x)
       have i₂ := eq33943
       grind)
    | exact superpose eq33943 eq23
    | exact resolve eq23 eq33943
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq23 eq33943
  have eq33985 : (τ (σ x)) = (k (τ (σ x)) (M.op (τ (σ y)) (τ (σ y)))) := by
    first
    | (have i₁ := eq33981
       have i₂ := eq18644 (σ y)
       grind)
    | exact superpose eq18644 eq33981
    | exact resolve eq33981 eq18644
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18644 eq33981
  have eq33996 : (τ (σ x)) = (k (τ (σ x)) (M.op y y)) := by
    first
    | (have i₁ := eq33985
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq33985
    | exact resolve eq33985 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33985
  have eq34002 : x = (k x (M.op y y)) := by
    first
    | (have i₁ := eq33996
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq33996
    | exact resolve eq33996 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33996
  have eq34017 : x = (M.op x y) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq34002
       have i₂ := eq100 y y x
       grind)
    | exact superpose eq100 eq34002
    | (have j1 := eq100 y y x
       grind)
    | exact resolve eq34002 eq100
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq100
  have eq34019 : ∀ X0 : G, x = (M.op x y) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq34002
       have i₂ := eq27295 y y x X0
       grind)
    | exact superpose eq27295 eq34002
    | (have j1 := eq27295 y x x X0
       grind)
    | exact resolve eq34002 eq27295
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq27295 eq34002
  have eq34114 : (σ x) = (M.op (σ x) (σ x)) ∨ (M.op x y) = (M.op y y) := by
    first
    | (have i₁ := eq142 x y
       have i₂ := eq34017
       grind)
    | exact superpose eq34017 eq142
    | exact resolve eq142 eq34017
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq142 eq34017
  have eq34326 : ∀ X0 : G, x = (M.op x x) ∨ (M.op X0 y) = (M.op X0 x) := by
    intro X0
    first
    | (have i₁ := eq53 y x
       have i₂ := eq34019 X0
       grind)
    | exact superpose eq34019 eq53
    | (have j1 := eq34019 X0
       grind)
    | exact resolve eq53 eq34019
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq53
  have eq34525 : x ≠ (M.op x x) ∨ (M.op x y) = (M.op x x) := by
    first
    | (have j0 := eq34019 x
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34019
  have eq34861 : (M.op x y) = (M.op x x) := by
    first
    | (have j1 := eq34326 x
       grind)
    | (have r₁ := eq34525
       have r₂ := eq34326 x
       grind)
    | exact resolve eq34525 eq34326
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34326 eq34525
  have eq34872 : (M.op (σ x) (σ y)) ≠ (σ (M.op x x)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq34861
       grind)
    | exact superpose eq34861 eq16
    | exact resolve eq16 eq34861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq35080 : (M.op (σ x) (σ y)) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq34872
       have i₂ := eq18645 x
       grind)
    | exact superpose eq18645 eq34872
    | exact resolve eq34872 eq18645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34872
  have eq35985 : (M.op y y) = (M.op x x) ∨ (σ x) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq34114
       have i₂ := eq34861
       grind)
    | exact superpose eq34861 eq34114
    | exact resolve eq34114 eq34861
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34114 eq34861
  have eq39426 : (σ x) ≠ (M.op (σ x) (σ x)) ∨ (M.op (σ x) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have j0 := eq33972 (σ x)
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq33972
  have eq39437 : (σ x) ≠ (M.op (σ x) (σ x)) := by
    first
    | (have r₁ := eq39426
       have r₂ := eq35080
       grind)
    | exact resolve eq39426 eq35080
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39426
  have eq39524 : (M.op y y) = (M.op x x) := by
    first
    | (have r₁ := eq35985
       have r₂ := eq39437
       grind)
    | exact resolve eq35985 eq39437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35985 eq39437
  have eq39578 : (σ (M.op x x)) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq18645 y
       have i₂ := eq39524
       grind)
    | exact superpose eq39524 eq18645
    | exact resolve eq18645 eq39524
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39524
  have eq39745 : (M.op (σ y) (σ y)) = (M.op (σ x) (σ x)) := by
    first
    | (have i₁ := eq39578
       have i₂ := eq18645 x
       grind)
    | exact superpose eq18645 eq39578
    | exact resolve eq39578 eq18645
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq18645 eq39578
  have eq41321 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (M.op (σ x) (σ x))) := by
    intro X0
    first
    | (have i₁ := eq51 (σ y) (σ y) X0
       have i₂ := eq39745
       grind)
    | exact superpose eq39745 eq51
    | exact resolve eq51 eq39745
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq39745
  have eq41456 : ∀ X0 : G, (M.op X0 (σ y)) = (M.op X0 (σ x)) := by
    intro X0
    first
    | (have i₁ := eq41321 X0
       have i₂ := eq51 (σ x) (σ x) X0
       grind)
    | exact superpose eq51 eq41321
    | exact resolve eq41321 eq51
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq51 eq41321
  have eq41507 : False := by grind
  exact eq41507

/-- `Equation3962`: `x ◇ y = (y ◇ (y ◇ x)) ◇ y`.  Vampire refutation replayed step by step.

`x □ y = if m(X,X) = Y then m(X,Y) else if m(Y,Y) = X then m(X,Y) else m(Y,X)`, writing `X`, `Y` for `x`, `y`.
The obligation names no target, so any law the companion satisfies is one more cell for free. -/
theorem GuardAut2_pxx_y_pyy_x_pxy_pxy_pyx_Equation3962 :
    AutBox.GuardAut2 ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0)) Law3962 := by
  classical
  refine AutBox.guardAut2_of ((Lf 0) ⋆ (Lf 0)) (Lf 1) ((Lf 1) ⋆ (Lf 1)) (Lf 0) ((Lf 0) ⋆ (Lf 1)) ((Lf 0) ⋆ (Lf 1)) ((Lf 1) ⋆ (Lf 0))
    (fun {G} _ M hM σ τ hi1 hi2 k hc1 hc2 hc3 hcom x y ↦ ?_)
  have hm := (@Law3962.models_iff G M).mp hM
  have ht : ∀ a b : G, M.op a a ≠ b ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).symm.imp id (hc1 a b)
  have hu : ∀ a b : G, M.op a a = b ∨ M.op b b ≠ a ∨ k a b = M.op a b :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).symm.imp id (fun hg2 ↦ hc2 a b hg hg2))
  have hv : ∀ a b : G, M.op a a = b ∨ M.op b b = a ∨ k a b = M.op b a :=
    fun a b ↦ (eq_or_ne (M.op a a) (b)).imp id
      (fun hg ↦ (eq_or_ne (M.op b b) (a)).imp id (fun hg2 ↦ hc3 a b hg hg2))
  have hd := hcom
  clear hc1 hc2 hc3 hcom
  by_contra nh
  have eq9 : ∀ X0 X1 : G, (M.op X0 X1) = (M.op (M.op X1 (M.op X1 X0)) X1) := by
    intro X0 X1
    grind
  have eq10 : ∀ X0 : G, (τ (σ X0)) = X0 := by
    intro X0
    grind
  have eq11 : ∀ X0 : G, (σ (τ X0)) = X0 := by
    intro X0
    grind
  have eq12 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X0 X0) ≠ X1 := by
    intro X0 X1
    grind
  have eq13 : ∀ X0 X1 : G, (M.op X0 X1) = (k X0 X1) ∨ (M.op X1 X1) ≠ X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    grind
  have eq14 : ∀ X0 X1 : G, (M.op X1 X0) = (k X0 X1) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
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
  have eq25 : ∀ X0 X1 : G, (k (τ X0) X1) = (τ (k X0 (σ X1))) := by
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
  have eq35 : ∀ X0 X1 : G, (k (τ X1) (τ X0)) = (τ (k X1 X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq25 X1 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq25
    | exact resolve eq25 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq57 : ∀ X0 X1 : G, (σ (k X1 X0)) = (M.op (σ X0) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) := by
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
  have eq59 : ∀ X0 X1 : G, (k X1 (σ X0)) = (σ (M.op X0 (τ X1))) ∨ (M.op X0 X0) = (τ X1) ∨ (M.op (τ X1) (τ X1)) = X0 := by
    intro X0 X1
    first
    | (have i₁ := eq19 X1 X0
       have i₂ := eq14 (τ X1) X0
       grind)
    | exact superpose eq14 eq19
    | (have j1 := eq14 (τ X1) X0
       grind)
    | exact resolve eq19 eq14
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq90 : ∀ X0 : G, (σ X0) = (M.op (M.op (σ X0) (σ X0)) (M.op (σ X0) (σ X0))) ∨ (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    grind
  have eq205 : (σ (M.op x y)) ≠ (σ (k y x)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) := by
    first
    | (have i₁ := eq16
       have i₂ := eq57 x y
       grind)
    | exact superpose eq57 eq16
    | (have j1 := eq57 x y
       grind)
    | exact resolve eq16 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq208 : ∀ X0 X1 : G, (M.op (σ X0) (σ X1)) = (M.op (M.op (σ X1) (σ (k X0 X1))) (σ X1)) ∨ (σ X0) = (M.op (σ X1) (σ X1)) ∨ (σ X1) = (M.op (σ X0) (σ X0)) := by
    intro X0 X1
    first
    | (have i₁ := eq9 (σ X0) (σ X1)
       have i₂ := eq57 X1 X0
       grind)
    | exact superpose eq57 eq9
    | (have j1 := eq57 X1 X0
       grind)
    | exact resolve eq9 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq210 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    grind
  have eq212 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq57 X0 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq213 : ∀ X0 : G, (σ X0) ≠ (σ (k X0 X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq212 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq212
  have eq215 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (k (σ X0) (σ (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq210 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq210
  have eq217 : ∀ X0 : G, (M.op (σ X0) (σ (k X0 X0))) = (σ (k X0 (k X0 X0))) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq215 X0
       have i₂ := eq15 X0 (k X0 X0)
       grind)
    | exact superpose eq15 eq215
    | (have j0 := eq215 X0
       grind)
    | exact resolve eq215 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq215
  have eq449 : ∀ X0 X1 : G, (k (σ X0) (σ X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq59 X0 (σ X0)
       have i₂ := eq10 X0
       grind)
    | exact superpose eq10 eq59
    | exact resolve eq59 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq59
  have eq484 : ∀ X0 X1 : G, (σ (k X0 X1)) = (σ (M.op X1 X0)) ∨ (M.op X1 X1) = X0 ∨ (M.op X0 X0) = X1 := by
    intro X0 X1
    first
    | (have i₁ := eq449 X0 X1
       have i₂ := eq15 X0 X1
       grind)
    | exact superpose eq15 eq449
    | (have j0 := eq449 X0 X1
       grind)
    | exact resolve eq449 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq449
  have eq730 : (σ (M.op x y)) ≠ (σ (M.op x y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ y = (M.op x x) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq205
       have i₂ := eq484 y x
       grind)
    | exact superpose eq484 eq205
    | (have j1 := eq484 (σ y) (σ x)
       grind)
    | (have r₁ := eq205
       have r₂ := eq484 y x
       grind)
    | exact resolve eq205 eq484
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq205 eq484
  have eq731 : y = (M.op x x) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by grind
  clear eq730
  have eq1166 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (M.op (σ (k X0 (k X0 X0))) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq208 X0 X0
       have i₂ := eq217 X0
       grind)
    | exact superpose eq217 eq208
    | (have j0 := eq208 X0 X0
       have j1 := eq217 X0
       grind)
    | exact resolve eq208 eq217
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq208 eq217
  have eq1184 : ∀ X0 : G, (σ X0) = (M.op (σ X0) (σ X0)) ∨ (M.op (σ X0) (σ X0)) = (M.op (σ (k X0 (k X0 X0))) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq1166 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq1166
  have eq4992 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (M.op (σ (k (τ X0) (k (τ X0) (τ X0)))) X0) := by
    intro X0
    first
    | (have i₁ := eq1184 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq1184
    | exact resolve eq1184 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5014 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (M.op (σ (k X0 (k X0 X0))) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq1184 x
       have i₂ := eq57 x x
       grind)
    | exact superpose eq57 eq1184
    | (have j0 := eq1184 X0
       have j1 := eq57 X0 X0
       grind)
    | exact resolve eq1184 eq57
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq57 eq1184
  have eq5032 : ∀ X0 : G, (σ X0) = (σ (k X0 X0)) ∨ (σ (k X0 X0)) = (M.op (σ (k X0 (k X0 X0))) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq5014 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5014
  have eq5039 : ∀ X0 : G, (σ (k X0 X0)) = (M.op (σ (k X0 (k X0 X0))) (σ X0)) ∨ (σ X0) = (M.op (σ X0) (σ X0)) := by
    intro X0
    first
    | (have j0 := eq5032 X0
       have j1 := eq213 X0
       grind)
    | (have r₁ := eq5032 X0
       have r₂ := eq213 X0
       grind)
    | exact resolve eq5032 eq213
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq213 eq5032
  have eq5042 : ∀ X0 : G, (M.op X0 X0) = (M.op (k X0 (σ (k (τ X0) (τ X0)))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq4992 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq4992
    | (have j0 := eq4992 X0
       grind)
    | exact resolve eq4992 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq4992
  have eq5043 : ∀ X0 : G, (M.op X0 X0) = (M.op (k X0 (k (σ (τ X0)) X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5042 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq5042
    | (have j0 := eq5042 X0
       grind)
    | exact resolve eq5042 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5042
  have eq5044 : ∀ X0 : G, (M.op X0 X0) = (M.op (k X0 (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5043 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5043
    | (have j0 := eq5043 X0
       grind)
    | exact resolve eq5043 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5043
  have eq5495 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (M.op (σ (k (τ X0) (k (τ X0) (τ X0)))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5039 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5039
    | exact resolve eq5039 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5039
  have eq5539 : ∀ X0 : G, (σ (k (τ X0) (τ X0))) = (M.op (k X0 (σ (k (τ X0) (τ X0)))) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5495 X0
       have i₂ := eq19 X0 (k (τ X0) (τ X0))
       grind)
    | exact superpose eq19 eq5495
    | (have j0 := eq5495 X0
       grind)
    | exact resolve eq5495 eq19
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq19 eq5495
  have eq5554 : ∀ X0 : G, (k (σ (τ X0)) X0) = (M.op (k X0 (k (σ (τ X0)) X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5539 X0
       have i₂ := eq20 X0 (τ X0)
       grind)
    | exact superpose eq20 eq5539
    | (have j0 := eq5539 X0
       grind)
    | exact resolve eq5539 eq20
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq20 eq5539
  have eq5563 : ∀ X0 : G, (k X0 X0) = (M.op (k X0 (k X0 X0)) X0) ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5554 X0
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq5554
    | (have j0 := eq5554 X0
       grind)
    | exact resolve eq5554 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5554
  have eq5598 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = X0 ∨ (M.op X0 X0) = X0 := by
    intro X0
    first
    | (have i₁ := eq5044 X0
       have i₂ := eq5563 X0
       grind)
    | exact superpose eq5563 eq5044
    | (have j0 := eq5044 X0
       have j1 := eq5563 X0
       grind)
    | exact resolve eq5044 eq5563
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5044 eq5563
  have eq5612 : ∀ X0 : G, (M.op X0 X0) = X0 ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5598 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5598
  have eq5757 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) ∨ (M.op X0 X0) = (k X0 X0) := by
    intro X0
    grind
  clear eq5612
  have eq5780 : ∀ X0 : G, (M.op X0 X0) = (k X0 X0) := by
    intro X0
    first
    | (have j0 := eq5757 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5757
  have eq5831 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq15 X0 X0
       have i₂ := eq5780 (σ X0)
       grind)
    | exact superpose eq5780 eq15
    | exact resolve eq15 eq5780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5838 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (k X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq35 X0 X0
       have i₂ := eq5780 (τ X0)
       grind)
    | exact superpose eq5780 eq35
    | exact resolve eq35 eq5780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq5890 : ∀ X0 : G, (M.op (τ X0) (τ X0)) = (τ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5838 X0
       have i₂ := eq5780 X0
       grind)
    | exact superpose eq5780 eq5838
    | exact resolve eq5838 eq5780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5838
  have eq5896 : ∀ X0 : G, (M.op (σ X0) (σ X0)) = (σ (M.op X0 X0)) := by
    intro X0
    first
    | (have i₁ := eq5831 X0
       have i₂ := eq5780 X0
       grind)
    | exact superpose eq5780 eq5831
    | exact resolve eq5831 eq5780
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5780 eq5831
  have eq6435 : ∀ X0 : G, (k (σ X0) (σ (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  have eq6474 : ∀ X0 : G, (σ (k X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    first
    | (have i₁ := eq6435 X0
       have i₂ := eq15 X0 (M.op X0 X0)
       grind)
    | exact superpose eq15 eq6435
    | exact resolve eq6435 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6435
  have eq6504 : ∀ X0 : G, (σ (M.op X0 (M.op X0 X0))) = (M.op (σ X0) (σ (M.op X0 X0))) := by
    intro X0
    grind
  clear eq6474
  have eq24797 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (τ (M.op (M.op X0 X0) X0)) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq90 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq90
    | exact resolve eq90 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq90
  have eq24997 : ∀ X0 : G, (M.op (M.op X0 X0) (M.op X0 X0)) = X0 ∨ (τ (M.op (M.op X0 X0) X0)) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq24797 X0
       have i₂ := eq35 X0 (M.op X0 X0)
       grind)
    | exact superpose eq35 eq24797
    | (have j0 := eq24797 X0
       grind)
    | exact resolve eq24797 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq24797
  have eq34576 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) ∨ (τ (M.op (M.op X0 X0) X0)) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    grind
  clear eq24997
  have eq75125 : ∀ X0 : G, (k (τ (M.op (σ X0) (σ X0))) X0) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) ∨ (τ (k (M.op (σ X0) (σ X0)) (σ X0))) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq25 (M.op (σ X0) (σ X0)) X0
       have i₂ := eq34576 (σ X0)
       grind)
    | exact superpose eq34576 eq25
    | (have j1 := eq34576 (σ X0)
       grind)
    | exact resolve eq25 eq34576
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq34576
  have eq75223 : ∀ X0 : G, (k (τ (σ (M.op X0 X0))) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (τ (k (M.op (σ X0) (σ X0)) (σ X0))) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq75125 X0
       have i₂ := eq5896 X0
       grind)
    | exact superpose eq5896 eq75125
    | (have j0 := eq75125 X0
       grind)
    | exact resolve eq75125 eq5896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75125
  have eq75273 : ∀ X0 : G, (k (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (τ (k (M.op (σ X0) (σ X0)) (σ X0))) = (τ (M.op (M.op (σ X0) (σ X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq75223 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq75223
    | (have j0 := eq75223 X0
       grind)
    | exact resolve eq75223 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75223
  have eq75321 : ∀ X0 : G, (τ (M.op (σ (M.op X0 X0)) (σ X0))) = (τ (k (σ (M.op X0 X0)) (σ X0))) ∨ (k (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq75273 X0
       have i₂ := eq5896 X0
       grind)
    | exact superpose eq5896 eq75273
    | (have j0 := eq75273 X0
       grind)
    | exact resolve eq75273 eq5896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75273
  have eq75364 : ∀ X0 : G, (k (τ (σ (M.op X0 X0))) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (k (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq75321 X0
       have i₂ := eq25 (σ (M.op X0 X0)) X0
       grind)
    | exact superpose eq25 eq75321
    | (have j0 := eq75321 X0
       grind)
    | exact resolve eq75321 eq25
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq25 eq75321
  have eq75387 : ∀ X0 : G, (k (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) ∨ (k (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq75364 X0
       have i₂ := eq10 (M.op X0 X0)
       grind)
    | exact superpose eq10 eq75364
    | (have j0 := eq75364 X0
       grind)
    | exact resolve eq75364 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75364
  have eq75388 : ∀ X0 : G, (k (M.op X0 X0) X0) = (τ (M.op (σ (M.op X0 X0)) (σ X0))) := by
    intro X0
    first
    | (have j0 := eq75387 X0
       grind)
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75387
  have eq75492 : ∀ X0 : G, (k (M.op (τ X0) (τ X0)) (τ X0)) = (τ (M.op (σ (M.op (τ X0) (τ X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq75388 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq75388
    | exact resolve eq75388 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq75559 : ∀ X0 : G, (σ (k (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq11 (M.op (σ (M.op X0 X0)) (σ X0))
       have i₂ := eq75388 X0
       grind)
    | exact superpose eq75388 eq11
    | exact resolve eq11 eq75388
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75388
  have eq75808 : ∀ X0 : G, (k (τ (M.op X0 X0)) (τ X0)) = (τ (M.op (σ (τ (M.op X0 X0))) X0)) := by
    intro X0
    first
    | (have i₁ := eq75492 X0
       have i₂ := eq5890 X0
       grind)
    | exact superpose eq5890 eq75492
    | exact resolve eq75492 eq5890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75492
  have eq75902 : ∀ X0 : G, (τ (M.op (M.op X0 X0) X0)) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq75808 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq75808
    | exact resolve eq75808 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75808
  have eq75963 : ∀ X0 : G, (τ (M.op (M.op X0 X0) X0)) = (τ (k (M.op X0 X0) X0)) := by
    intro X0
    first
    | (have i₁ := eq75902 X0
       have i₂ := eq35 X0 (M.op X0 X0)
       grind)
    | exact superpose eq35 eq75902
    | exact resolve eq75902 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75902
  have eq76765 : ∀ X0 : G, (k (M.op X0 X0) X0) = (σ (τ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq11 (k (M.op X0 X0) X0)
       have i₂ := eq75963 X0
       grind)
    | exact superpose eq75963 eq11
    | exact resolve eq11 eq75963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77064 : ∀ X0 : G, (M.op (M.op X0 X0) X0) = (k (M.op X0 X0) X0) := by
    intro X0
    first
    | (have i₁ := eq76765 X0
       have i₂ := eq11 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq11 eq76765
    | exact resolve eq76765 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq76765
  have eq77259 : ∀ X0 : G, (M.op (τ (M.op X0 X0)) (τ X0)) = (k (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq77064 (τ X0)
       have i₂ := eq5890 X0
       grind)
    | exact superpose eq5890 eq77064
    | exact resolve eq77064 eq5890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  have eq77392 : ∀ X0 : G, (τ (k (M.op X0 X0) X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq77259 X0
       have i₂ := eq35 X0 (M.op X0 X0)
       grind)
    | exact superpose eq35 eq77259
    | exact resolve eq77259 eq35
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq35 eq77259
  have eq77448 : ∀ X0 : G, (τ (M.op (M.op X0 X0) X0)) = (M.op (τ (M.op X0 X0)) (τ X0)) := by
    intro X0
    first
    | (have i₁ := eq77392 X0
       have i₂ := eq75963 X0
       grind)
    | exact superpose eq75963 eq77392
    | exact resolve eq77392 eq75963
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75963 eq77392
  have eq78448 : ∀ X0 : G, (σ (k (σ (M.op X0 X0)) (σ X0))) = (M.op (σ (σ (M.op X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq75559 (σ X0)
       have i₂ := eq5896 X0
       grind)
    | exact superpose eq5896 eq75559
    | exact resolve eq75559 eq5896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq75559
  have eq78673 : ∀ X0 : G, (σ (σ (k (M.op X0 X0) X0))) = (M.op (σ (σ (M.op X0 X0))) (σ (σ X0))) := by
    intro X0
    first
    | (have i₁ := eq78448 X0
       have i₂ := eq15 (M.op X0 X0) X0
       grind)
    | exact superpose eq15 eq78448
    | exact resolve eq78448 eq15
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78448
  have eq78774 : ∀ X0 : G, (M.op (σ (σ (M.op X0 X0))) (σ (σ X0))) = (σ (σ (M.op (M.op X0 X0) X0))) := by
    intro X0
    first
    | (have i₁ := eq78673 X0
       have i₂ := eq77064 X0
       grind)
    | exact superpose eq77064 eq78673
    | exact resolve eq78673 eq77064
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77064 eq78673
  have eq88910 : ∀ X0 : G, (σ (σ (M.op (M.op (τ X0) (τ X0)) (τ X0)))) = (M.op (σ (σ (M.op (τ X0) (τ X0)))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq78774 (τ X0)
       have i₂ := eq11 X0
       grind)
    | exact superpose eq11 eq78774
    | exact resolve eq78774 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq78774
  have eq89076 : ∀ X0 : G, (M.op (σ (σ (τ (M.op X0 X0)))) (σ X0)) = (σ (σ (M.op (τ (M.op X0 X0)) (τ X0)))) := by
    intro X0
    first
    | (have i₁ := eq88910 X0
       have i₂ := eq5890 X0
       grind)
    | exact superpose eq5890 eq88910
    | exact resolve eq88910 eq5890
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5890 eq88910
  have eq89152 : ∀ X0 : G, (M.op (σ (σ (τ (M.op X0 X0)))) (σ X0)) = (σ (σ (τ (M.op (M.op X0 X0) X0)))) := by
    intro X0
    first
    | (have i₁ := eq89076 X0
       have i₂ := eq77448 X0
       grind)
    | exact superpose eq77448 eq89076
    | exact resolve eq89076 eq77448
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq77448 eq89076
  have eq89218 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (σ (τ (M.op X0 X0)))) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq89152 X0
       have i₂ := eq11 (M.op (M.op X0 X0) X0)
       grind)
    | exact superpose eq11 eq89152
    | exact resolve eq89152 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89152
  have eq89262 : ∀ X0 : G, (σ (M.op (M.op X0 X0) X0)) = (M.op (σ (M.op X0 X0)) (σ X0)) := by
    intro X0
    first
    | (have i₁ := eq89218 X0
       have i₂ := eq11 (M.op X0 X0)
       grind)
    | exact superpose eq11 eq89218
    | exact resolve eq89218 eq11
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89218
  have eq420766 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq6504 x
       have i₂ := eq731
       grind)
    | exact superpose eq731 eq6504
    | exact resolve eq6504 eq731
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq731
  have eq421180 : (σ x) = (M.op (σ y) (σ y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have r₁ := eq420766
       have r₂ := eq16
       grind)
    | exact resolve eq420766 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq420766
  have eq421426 : (σ x) = (σ (M.op y y)) ∨ (σ y) = (M.op (σ x) (σ x)) ∨ x = (M.op y y) := by
    first
    | (have i₁ := eq421180
       have i₂ := eq5896 y
       grind)
    | exact superpose eq5896 eq421180
    | exact resolve eq421180 eq5896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421180
  have eq421466 : x = (M.op y y) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq421426
       have i₂ := eq5896 x
       grind)
    | exact superpose eq5896 eq421426
    | exact resolve eq421426 eq5896
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq5896 eq421426
  have eq421721 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) ∨ (σ y) = (σ (M.op x x)) := by
    first
    | (have i₁ := eq89262 y
       have i₂ := eq421466
       grind)
    | exact superpose eq421466 eq89262
    | exact resolve eq89262 eq421466
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421466
  have eq421749 : (σ y) = (σ (M.op x x)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq421721
       have r₂ := eq16
       grind)
    | exact resolve eq421721 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421721
  have eq425921 : (M.op x x) = (τ (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq10 (M.op x x)
       have i₂ := eq421749
       grind)
    | exact superpose eq421749 eq10
    | exact resolve eq10 eq421749
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq421749
  have eq426437 : y = (M.op x x) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq425921
       have i₂ := eq10 y
       grind)
    | exact superpose eq10 eq425921
    | exact resolve eq425921 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq425921
  have eq426768 : (σ (M.op x y)) = (M.op (σ x) (σ y)) ∨ (σ x) = (σ (M.op y y)) := by
    first
    | (have i₁ := eq6504 x
       have i₂ := eq426437
       grind)
    | exact superpose eq426437 eq6504
    | exact resolve eq6504 eq426437
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq6504 eq426437
  have eq426975 : (σ x) = (σ (M.op y y)) := by
    first
    | (have r₁ := eq426768
       have r₂ := eq16
       grind)
    | exact resolve eq426768 eq16
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426768
  have eq431459 : (M.op y y) = (τ (σ x)) := by
    first
    | (have i₁ := eq10 (M.op y y)
       have i₂ := eq426975
       grind)
    | exact superpose eq426975 eq10
    | exact resolve eq10 eq426975
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq426975
  have eq431981 : x = (M.op y y) := by
    first
    | (have i₁ := eq431459
       have i₂ := eq10 x
       grind)
    | exact superpose eq10 eq431459
    | exact resolve eq431459 eq10
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq431459
  have eq432689 : (σ (M.op x y)) = (M.op (σ x) (σ y)) := by
    first
    | (have i₁ := eq89262 y
       have i₂ := eq431981
       grind)
    | exact superpose eq431981 eq89262
    | exact resolve eq89262 eq431981
    | grind
    | grind (splits := 40)
    | grind (splits := 40) (ematch := 20)
  clear eq89262 eq431981
  have eq432716 : False := by grind
  exact eq432716
